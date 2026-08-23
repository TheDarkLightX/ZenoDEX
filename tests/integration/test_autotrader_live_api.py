from __future__ import annotations

import json
import threading

import pytest

import src.integration.autotrader_live_api as autotrader_live_api
from src.agents.intent_signer import sign_intent
from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.integration.autotrader_live_api import handle_autotrader_live_request
from src.integration.autotrader_supervisor_profile import build_autotrader_supervisor_profile_v1
from src.integration.operations import (
    SignedIntentEnvelope,
    create_signed_intent_operation,
    parse_intents,
)
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from src.state.canonical import canonical_json_bytes
from src.state.intents import Intent, IntentKind

_STAGE_CERT_HASH = "0x" + "5a" * 32
_RELEASE_CERT_HASH = "0x" + "98" * 32


@pytest.fixture(autouse=True)
def _isolated_execution_journal(monkeypatch: pytest.MonkeyPatch, tmp_path) -> None:
    monkeypatch.setenv(
        "AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH",
        str(tmp_path / "autotrader-execution-journal.jsonl"),
    )


def test_intent_to_obj_has_nested_signing_and_json_parity() -> None:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "37" * 32,
        sender_pubkey="0x" + "37" * 48,
        deadline=10,
        fields={
            "nonce": 1,
            "route": {
                "assets": ["asset-a", "asset-b"],
                "limits": {"amount_in": 7, "min_amount_out": 6},
            },
        },
    )

    rendered = autotrader_live_api._intent_to_obj(intent)

    json.dumps(rendered, sort_keys=True)
    assert canonical_json_bytes(
        build_dex_intent_signing_dict_v1(rendered)
    ) == canonical_json_bytes(build_dex_intent_signing_dict_v1(intent))
    assert type(rendered["fields"]["route"]) is dict
    assert type(rendered["fields"]["route"]["assets"]) is list


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
    signer_privkey: int = 7,
) -> dict[str, object]:
    return {
        "ok": True,
        "status": "prepared",
        "surface": "autotrader_live_prepare",
        "report": {
            "schema": "zenodex/autotrader-live-api-report/v1",
            "mode": "live_prepare",
            "signing": {
                "chain_id": "tau-local",
                "signer_pubkey": "0x" + bls_pubkey_hex_from_privkey(signer_privkey),
            },
            "decision": {"tag": "submit"},
            "user_rule_summary": {
                "intent": {
                    "template": template,
                    "allowed_actions": list(allowed_actions or ["PLACE_SWAP_EXACT_IN"]),
                },
                "sizing": {"per_order_max": 100},
                "budget": {"per_window_max": 500, "lifetime_max": 1000},
                "window": {
                    "valid_from_epoch": 1,
                    "valid_until_epoch": 100,
                    "min_order_spacing_epochs": 4,
                },
                "controls": {"kill_switch_enabled": True},
            },
            "operations": {"5": [{"kind": "PLACE_SWAP_EXACT_IN"}]},
            "stage_certificate": {"stage_hash": _STAGE_CERT_HASH},
            "live_release_certificate": {"release_hash": _RELEASE_CERT_HASH, "release_ok": True},
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
    assert payload["status"]["prepare_budget"]["max_concurrent"] >= 1
    assert "production_chain_submission" in payload["status"]["not_claimed"]


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


def test_autotrader_live_prepare_requires_explicit_signer_privkey(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps({"acknowledge_experimental_live_risk": True}).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "missing_signer_privkey"


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


def test_autotrader_live_prepare_rejects_when_concurrency_budget_exhausted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    entered = threading.Event()
    release = threading.Event()
    finished: list[tuple[int, dict[str, object]]] = []

    def slow_prepare(_body: object) -> dict[str, object]:
        entered.set()
        assert release.wait(timeout=5)
        return {"ok": True, "status": "prepared"}

    monkeypatch.setenv("AUTOTRADER_LIVE_PREPARE_MAX_CONCURRENT", "1")
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response_inner", slow_prepare)

    def first_prepare() -> None:
        finished.append(
            handle_autotrader_live_request(
                "POST",
                "/api/strategy/autotrader/prepare",
                json.dumps({"acknowledge_experimental_live_risk": True}).encode("utf-8"),
            )
        )

    thread = threading.Thread(target=first_prepare)
    thread.start()
    assert entered.wait(timeout=5)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps({"acknowledge_experimental_live_risk": True}).encode("utf-8"),
    )

    release.set()
    thread.join(timeout=5)

    assert status == 429
    assert payload["ok"] is False
    assert payload["error"] == "autotrader_prepare_busy"
    assert payload["prepare_budget"] == {"max_concurrent": 1, "in_flight": 1, "available": 0}
    assert finished == [(200, {"ok": True, "status": "prepared"})]


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
    assert payload["submission"]["wire_tau_tx_payload"]["operations"].get("5")
    assert "2" not in payload["submission"]["wire_tau_tx_payload"]["operations"]
    assert payload["submission"]["createblock_response"] == "SUCCESS: Block created."
    assert len(_FakeTauClient.sent) == 1
    assert _FakeTauClient.sent[0] == payload["submission"]["wire_tau_tx_payload"]
    assert _FakeTauClient.mined == 1


def test_autotrader_live_submit_rebuilds_once_on_stale_sequence(
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
            if len(type(self).sent) == 1:
                return "FAILURE: Invalid sequence number: expected 10, got 9."
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
    assert payload["report"]["tau_tx_payload"]["sequence_number"] == 10
    assert payload["submission"]["sendtx_response"] == "FAILURE: Invalid sequence number: expected 10, got 9."
    assert payload["submission"]["retry_sendtx_response"] == "SUCCESS: Transaction queued."
    assert payload["submission"]["retry_sequence_error"] == {"expected": 10, "got": 9}
    assert payload["submission"]["wire_tau_tx_payload"]["sequence_number"] == 10
    assert payload["submission"]["initial_wire_tau_tx_payload"]["sequence_number"] == 9
    assert len(_FakeTauClient.sent) == 2
    assert _FakeTauClient.sent[0]["sequence_number"] == 9
    assert _FakeTauClient.sent[1]["sequence_number"] == 10
    assert _FakeTauClient.mined == 1


def test_autotrader_live_prepare_accepts_hex_private_key(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/prepare",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": hex(7),
                "chain_id": "tau-local",
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["report"]["signing"]["signer_pubkey"] == "0x" + bls_pubkey_hex_from_privkey(7)


def test_autotrader_live_submit_rejects_failed_sendtx(
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
            return "REJECTED invalid signature"

    _FakeTauClient.sent = []
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
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

    assert status == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "sendtx_failed"
    assert payload["submission"]["sendtx_response"] == "REJECTED invalid signature"
    assert len(_FakeTauClient.sent) == 1


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


def test_autotrader_live_submit_rejects_external_prepared_report_without_local_signing(
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

    report = _mock_supervisor_prepare_payload()["report"]
    assert isinstance(report, dict)
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=report["operations"],
        fee_limit="0",
    )

    _FakeTauClient.sent = []
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "chain_id": "tau-local",
                "prepared_report": report,
                "signed_tau_tx_payload": external_payload,
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["status"] == "submit_rejected"
    assert payload["error"] == "external_prepared_report_untrusted"
    assert _FakeTauClient.sent == []


def test_autotrader_live_submit_rejects_external_prepared_report_chain_mismatch(
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

    report = json.loads(json.dumps(_mock_supervisor_prepare_payload()["report"]))
    assert isinstance(report, dict)
    assert isinstance(report["signing"], dict)
    report["signing"]["chain_id"] = "other-chain"
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=report["operations"],
        fee_limit="0",
    )

    _FakeTauClient.sent = []
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/submit",
        json.dumps(
            {
                "acknowledge_experimental_live_risk": True,
                "chain_id": "tau-local",
                "prepared_report": report,
                "signed_tau_tx_payload": external_payload,
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "external_prepared_report_untrusted"
    assert _FakeTauClient.sent == []


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
    tmp_path,
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
    journal = tmp_path / "autotrader-execution-journal.jsonl"
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
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
    rows = [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]
    assert [row["state"] for row in rows] == ["PENDING", "SENT"]

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


def test_autotrader_live_execute_once_deterministic_reject_does_not_reserve(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    journal = tmp_path / "autotrader-execution-journal.jsonl"
    execution_keys: set[str] = set()
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", raising=False)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "deterministic-reject",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
        execution_keys=execution_keys,
    )

    assert status == 400
    assert payload["error"] == "testnet_submission_disabled"
    assert execution_keys == set()
    assert not journal.exists()


def test_autotrader_live_execute_once_ambiguous_send_stays_pending_and_blocks_retry(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    class _FakeTauClient:
        attempts = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, _payload: object) -> str:
            type(self).attempts += 1
            return "ERROR: transport outcome unknown"

    journal = tmp_path / "autotrader-execution-journal.jsonl"
    execution_keys: set[str] = set()
    _FakeTauClient.attempts = 0
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)
    body = {
        "execution_id": "ambiguous-send",
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }

    first_status, first = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=execution_keys,
    )
    replay_status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )

    rows = [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]
    assert first_status == 400
    assert first["error"] == "sendtx_failed"
    assert first["execution"]["state"] == "PENDING"
    assert first["execution"]["reconciliation_required"] is True
    assert [row["state"] for row in rows] == ["PENDING"]
    assert replay_status == 400
    assert replay["error"] == "execution_replay"
    assert _FakeTauClient.attempts == 1


def test_autotrader_live_execute_once_fsync_failure_blocks_send(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    class _FakeTauClient:
        attempts = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, _payload: object) -> str:
            type(self).attempts += 1
            return "SUCCESS: Transaction queued."

    journal = tmp_path / "autotrader-execution-journal.jsonl"
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)
    monkeypatch.setattr(autotrader_live_api.os, "fsync", lambda _fd: (_ for _ in ()).throw(OSError("disk")))

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "fsync-failure",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert str(payload["error"]).startswith("execution_journal_write_failed:")
    assert _FakeTauClient.attempts == 0


def test_autotrader_live_execute_once_requires_durable_journal_before_send(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        attempts = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, _payload: object) -> str:
            type(self).attempts += 1
            return "SUCCESS: Transaction queued."

    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.delenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", raising=False)
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "journal-required",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["error"] == "execution_journal_path_required"
    assert _FakeTauClient.attempts == 0


def test_autotrader_live_execute_once_sent_marker_failure_quarantines_replay(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    class _FakeTauClient:
        attempts = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, _payload: object) -> str:
            type(self).attempts += 1
            return "SUCCESS: Transaction queued."

    journal = tmp_path / "autotrader-execution-journal.jsonl"
    journal.touch()
    fsync_calls = 0
    real_fsync = autotrader_live_api.os.fsync

    def fail_sent_marker(fd: int) -> None:
        nonlocal fsync_calls
        fsync_calls += 1
        if fsync_calls == 2:
            raise OSError("marker disk failure")
        real_fsync(fd)

    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)
    monkeypatch.setattr(autotrader_live_api.os, "fsync", fail_sent_marker)
    body = {
        "execution_id": "sent-marker-failure",
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }

    first_status, first = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )
    replay_status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )

    assert first_status == 400
    assert str(first["error"]).startswith("execution_journal_write_failed:")
    assert first["execution"]["state"] == "PENDING"
    assert first["execution"]["reconciliation_required"] is True
    assert replay_status == 400
    assert replay["error"] == "execution_replay"
    assert _FakeTauClient.attempts == 1


def test_autotrader_live_execute_once_mining_failure_preserves_sent_state(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    class _FakeTauClient:
        attempts = 0

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def sendtx(self, _payload: object) -> str:
            type(self).attempts += 1
            return "SUCCESS: Transaction queued."

        def createblock(self) -> str:
            return "ERROR: block creation unavailable"

    journal = tmp_path / "autotrader-execution-journal.jsonl"
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_AUTO_MINE", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)
    body = {
        "execution_id": "mining-observation-failure",
        "acknowledge_experimental_live_risk": True,
        "signer_privkey": 7,
        "chain_id": "tau-local",
        "tx_sequence_number": 9,
        "tx_expiration_time": 999,
        "last_used_nonce": 0,
    }

    first_status, first = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )
    replay_status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )

    rows = [json.loads(line) for line in journal.read_text(encoding="utf-8").splitlines()]
    assert first_status == 400
    assert first["error"] == "createblock_failed"
    assert first["execution"]["state"] == "SENT"
    assert first["execution"]["reconciliation_required"] is True
    assert [row["state"] for row in rows] == ["PENDING", "SENT"]
    assert replay_status == 400
    assert replay["error"] == "execution_replay"
    assert _FakeTauClient.attempts == 1


def test_execution_journal_rejects_surface_change(monkeypatch: pytest.MonkeyPatch, tmp_path) -> None:
    journal = tmp_path / "autotrader-execution-journal.jsonl"
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    autotrader_live_api._reserve_execution_id(
        set(),
        "surface-bound",
        surface="autotrader_live_execute_once",
    )

    with pytest.raises(ValueError, match="execution_journal_surface_mismatch"):
        autotrader_live_api._mark_execution_sent(
            "surface-bound",
            surface="autotrader_live_supervisor_execute",
        )


def test_autotrader_live_execute_once_v1_journal_row_blocks_replay(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    journal = tmp_path / "autotrader-execution-journal.jsonl"
    journal.write_text(
        json.dumps(
            {
                "schema": "zenodex/autotrader-execution-journal/v1",
                "execution_id": "legacy-consumed",
                "surface": "autotrader_live_execute_once",
                "consumed_at_unix_s": 1,
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps({"execution_id": "legacy-consumed"}).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["error"] == "execution_replay"


def test_autotrader_live_execute_once_rejects_replay_from_persistent_journal(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
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

    journal = tmp_path / "autotrader-execution-journal.jsonl"
    _FakeTauClient.sent = []
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(journal))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    body = {
        "execution_id": "journal-exec-1",
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
        execution_keys=set(),
    )
    assert status == 200
    assert accepted["ok"] is True
    assert journal.exists()

    status, replay = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(body).encode("utf-8"),
        execution_keys=set(),
    )
    assert status == 400
    assert replay["ok"] is False
    assert replay["error"] == "execution_replay"
    assert len(_FakeTauClient.sent) == 1


def test_autotrader_live_execute_once_journal_write_failure_blocks_send(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
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
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(tmp_path))
    monkeypatch.setattr(autotrader_live_api, "_execution_journal_ids", lambda: set())
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "journal-write-fails-before-send",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("execution_journal_write_failed:")
    assert _FakeTauClient.sent == []


def test_autotrader_live_execute_once_journal_read_failure_blocks_send(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
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
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_EXECUTION_JOURNAL_PATH", str(tmp_path))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/execute-once",
        json.dumps(
            {
                "execution_id": "journal-read-fails-before-send",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["ok"] is False
    assert str(payload["error"]).startswith("execution_journal_read_failed:")
    assert _FakeTauClient.sent == []


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
    assert payload["preflight"]["window_valid_from_epoch"] == 1
    assert payload["preflight"]["window_valid_until_epoch"] == 100
    assert payload["preflight"]["min_order_spacing_epochs"] == 4
    assert payload["preflight"]["per_order_max"] == 100
    assert payload["preflight"]["per_window_max"] == 500
    assert payload["preflight"]["lifetime_max"] == 1000
    assert payload["preflight"]["kill_switch_enabled"] is True
    assert payload["preflight"]["bounded_surface_hash"]
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


def test_autotrader_live_supervisor_preflight_counts_wire_encoded_operations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    report["operations"] = {
        "2": json.dumps(
            [
                {"kind": "PLACE_SWAP_EXACT_IN", "id": "a"},
                {"kind": "PLACE_SWAP_EXACT_IN", "id": "b"},
            ],
            sort_keys=True,
        )
    }
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-wire-ops",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_max_actions_per_tick_exceeded:2>1"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_missing_window_summary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    user_rule_summary = report["user_rule_summary"]
    assert isinstance(user_rule_summary, dict)
    user_rule_summary.pop("window", None)
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-missing-window",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_user_rule_window_missing"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_negative_order_spacing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    user_rule_summary = report["user_rule_summary"]
    assert isinstance(user_rule_summary, dict)
    window = user_rule_summary["window"]
    assert isinstance(window, dict)
    window["min_order_spacing_epochs"] = -1
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-negative-spacing",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_user_rule_window_invalid"
    assert payload["supervisor"]["supervisor_ready"] is True


@pytest.mark.parametrize(
    ("section", "field", "bad_value"),
    [
        ("window", "valid_from_epoch", True),
        ("window", "valid_until_epoch", True),
        ("window", "min_order_spacing_epochs", False),
        ("sizing", "per_order_max", True),
        ("budget", "per_window_max", True),
        ("budget", "lifetime_max", True),
    ],
)
def test_autotrader_live_supervisor_preflight_rejects_bool_bounded_surface_numbers(
    monkeypatch: pytest.MonkeyPatch,
    section: str,
    field: str,
    bad_value: bool,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    user_rule_summary = report["user_rule_summary"]
    assert isinstance(user_rule_summary, dict)
    section_obj = user_rule_summary[section]
    assert isinstance(section_obj, dict)
    section_obj[field] = bad_value
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": f"supervisor-preflight-bool-{section}-{field}",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_user_rule_budget_invalid"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_malformed_stage_hash(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    report["stage_certificate"] = {"stage_hash": "0xstage"}
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-bad-stage-hash",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_stage_certificate_hash_invalid"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_malformed_release_hash(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    report["live_release_certificate"] = {"release_hash": "0xrelease", "release_ok": True}
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-bad-release-hash",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_release_certificate_hash_invalid"
    assert payload["supervisor"]["supervisor_ready"] is True


def test_autotrader_live_supervisor_preflight_rejects_bad_release_certificate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    prepared_payload = _mock_supervisor_prepare_payload()
    report = prepared_payload["report"]
    assert isinstance(report, dict)
    report["live_release_certificate"] = {"release_hash": _RELEASE_CERT_HASH, "release_ok": False}
    monkeypatch.setattr(autotrader_live_api, "_build_prepare_response", lambda _body: prepared_payload)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/preflight",
        json.dumps(
            {
                "execution_id": "supervisor-preflight-bad-release",
                "acknowledge_experimental_live_risk": True,
                "signer_privkey": 7,
                "chain_id": "tau-local",
            }
        ).encode("utf-8"),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_release_certificate_not_ok"
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


def test_autotrader_live_supervisor_execute_rejects_untrusted_external_prepared_report(
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

    report = _mock_supervisor_prepare_payload()["report"]
    assert isinstance(report, dict)
    external_payload = build_signed_tau_transaction(
        privkey=7,
        sequence_number=9,
        expiration_time=999,
        operations=report["operations"],
        fee_limit="0",
    )

    _FakeTauClient.sent = []
    monkeypatch.delenv("AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING", raising=False)
    monkeypatch.setenv("AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_ENABLED", "true")
    monkeypatch.setenv("AUTOTRADER_LIVE_SUPERVISOR_PROFILE_JSON", json.dumps(_supervisor_profile(), sort_keys=True))
    monkeypatch.setattr(autotrader_live_api, "TauNetTcpClient", _FakeTauClient)

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(
            {
                "execution_id": "supervisor-external-prepared-1",
                "acknowledge_experimental_live_risk": True,
                "chain_id": "tau-local",
                "prepared_report": report,
                "signed_tau_tx_payload": external_payload,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "supervisor_external_prepared_report_untrusted"
    assert _FakeTauClient.sent == []


def test_autotrader_live_supervisor_execute_rejects_external_sender_mismatch(
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
        privkey=8,
        sequence_number=9,
        expiration_time=999,
        operations=prepared["report"]["operations"],
        fee_limit="0",
    )

    status, payload = handle_autotrader_live_request(
        "POST",
        "/api/strategy/autotrader/supervisor/execute",
        json.dumps(
            {
                "execution_id": "supervisor-external-sender-mismatch-1",
                "acknowledge_experimental_live_risk": True,
                **{k: v for k, v in prepare_body.items() if k not in {"tx_sequence_number", "tx_expiration_time"}},
                "signed_tau_tx_payload": external_payload,
            }
        ).encode("utf-8"),
        execution_keys=set(),
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == "signed_tau_tx_payload sender mismatch"
    assert _FakeTauClient.sent == []


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
    monkeypatch.setenv("TAU_DEX_ALLOW_MISSING_SETTLEMENT", "1")

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
    create_pool_intent_obj = parse_intents({"2": [create_pool_intent]})[0]
    create_pool_ops = create_signed_intent_operation(
        [
            SignedIntentEnvelope(
                intent=create_pool_intent_obj,
                signature=sign_intent(create_pool_intent_obj, signer_privkey, chain_id="tau-local").signature,
            )
        ]
    )
    ok, app_state_json, _app_hash, _balances_patch, err = plugin.apply_app_tx(
        app_state_json="",
        chain_balances={signer_raw: 1},
        operations={
            "7": {"mint": [[signer_pubkey, "A", 10_000], [signer_pubkey, "B", 10_000]]},
            "5": create_pool_ops["2"],
        },
        tx_sender_pubkey=signer_raw,
        block_timestamp=1,
    )
    assert ok is True, err
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
        operations=autotrader_live_api._upstream_safe_dex_operations(
            payload["report"]["operations"]
        ),
        tx_sender_pubkey=signer_raw,
        block_timestamp=10,
    )
    assert ok is True, err
    assert err is None
    assert _balance(next_app_state_json, pubkey=signer_pubkey, asset="A") == 8900


def test_autotrader_live_submit_accepts_background_mined_app_state_change(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeTauClient:
        sent: list[dict[str, object]] = []
        app_hash = "sha256:" + "11" * 32

        def __init__(self, _cfg: object) -> None:
            pass

        def get_sequence(self, _sender_pubkey_hex: str) -> int:
            return 9

        def getappstate(self, *, full: bool = False) -> str:
            assert full is True
            return json.dumps({"app_hash": type(self).app_hash, "app_state": {}}, sort_keys=True)

        def sendtx(self, payload: object) -> str:
            assert isinstance(payload, dict)
            type(self).sent.append(dict(payload))
            type(self).app_hash = "sha256:" + "22" * 32
            return "SUCCESS: Transaction queued."

        def createblock(self) -> str:
            return "Mempool is empty. No block created."

    _FakeTauClient.sent = []
    _FakeTauClient.app_hash = "sha256:" + "11" * 32
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
                "tx_sequence_number": 9,
                "tx_expiration_time": 999,
                "last_used_nonce": 0,
            }
        ).encode("utf-8"),
    )

    assert status == 200
    assert payload["ok"] is True
    assert payload["submission"]["createblock_response"] == "Mempool is empty. No block created."
    assert payload["submission"]["observed_app_hash_after_createblock"] == "sha256:" + "22" * 32
    assert len(_FakeTauClient.sent) == 1
