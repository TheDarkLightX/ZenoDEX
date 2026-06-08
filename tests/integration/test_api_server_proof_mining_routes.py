from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_proof_mining_routes import maybe_handle_proof_mining_route


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "claim": {"schema": "fake-claim"},
        "chain_balances": {"reward-pool": 20},
        "tx_sender_pubkey": "sender-pubkey",
        "expected_proposal_hash": "proposal-hash",
        "app_state_json": "",
    }
    request.update(overrides)
    return request


class _FakeStatus:
    def __init__(self, payload: dict[str, object]) -> None:
        self.payload = payload

    def to_public_dict(self) -> dict[str, object]:
        return self.payload


def _fail_on_proof_mining_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name == "src.integration.proof_mining_claimability":
            raise AssertionError("proof mining claimability imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_proof_mining_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_proof_mining_route(
        path="/api/dex/not_proof_mining_status",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_proof_mining_status_rejects_bad_fields_in_legacy_order_before_import(monkeypatch: Any) -> None:
    _fail_on_proof_mining_import(monkeypatch)

    cases = [
        (
            _request(
                claim=[],
                chain_balances=[],
                proof_mining_context={"context": "present"},
                app_state_json=[],
                tx_sender_pubkey="",
                expected_proposal_hash="",
            ),
            "bad_claim",
        ),
        (
            _request(
                chain_balances=[],
                proof_mining_context={"context": "present"},
                app_state_json=[],
                tx_sender_pubkey="",
                expected_proposal_hash="",
            ),
            "bad_chain_balances",
        ),
        (
            _request(
                proof_mining_context={"context": "present"},
                app_state_json=[],
                tx_sender_pubkey="",
                expected_proposal_hash="",
            ),
            "proof_mining_context_not_accepted",
        ),
        (_request(app_state_json=[], tx_sender_pubkey="", expected_proposal_hash=""), "bad_app_state_json"),
        (_request(tx_sender_pubkey="", expected_proposal_hash=""), "missing_tx_sender_pubkey"),
        (_request(expected_proposal_hash=""), "missing_expected_proposal_hash"),
    ]
    for obj, error in cases:
        writes, write_json = _capture()

        handled = maybe_handle_proof_mining_route(
            path="/api/dex/proof_mining_status",
            obj=obj,
            write_json=write_json,
        )

        assert handled is True
        assert writes == [(400, {"ok": False, "error": error})]


def test_proof_mining_status_success_and_arguments(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}
    status_payload = {"enabled": True, "claimable": False, "checks": {"runtime_apply_ok": False}}

    monkeypatch.setenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "  reward-pool-pubkey  ")

    def evaluate_proof_mining_claimability(**kwargs: object) -> _FakeStatus:
        captured.update(kwargs)
        return _FakeStatus(status_payload)

    monkeypatch.setattr(
        "src.integration.proof_mining_claimability.evaluate_proof_mining_claimability",
        evaluate_proof_mining_claimability,
    )

    obj = _request()
    handled = maybe_handle_proof_mining_route(
        path="/api/dex/proof_mining_status",
        obj=obj,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "reward_pool_pubkey": "reward-pool-pubkey",
        "app_state_json": "",
        "chain_balances": {"reward-pool": 20},
        "claim_artifact": {"schema": "fake-claim"},
        "tx_sender_pubkey": "sender-pubkey",
        "expected_proposal_hash": "proposal-hash",
        "proof_mining_context_obj": None,
    }
    assert writes == [(200, {"ok": True, "status": status_payload})]


def test_proof_mining_status_missing_env_passes_none(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    monkeypatch.delenv("TAU_DEX_PROOF_MINING_POOL_PUBKEY", raising=False)

    def evaluate_proof_mining_claimability(**kwargs: object) -> _FakeStatus:
        captured.update(kwargs)
        return _FakeStatus({"enabled": False})

    monkeypatch.setattr(
        "src.integration.proof_mining_claimability.evaluate_proof_mining_claimability",
        evaluate_proof_mining_claimability,
    )

    handled = maybe_handle_proof_mining_route(
        path="/api/dex/proof_mining_status",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert captured["reward_pool_pubkey"] is None
    assert writes == [(200, {"ok": True, "status": {"enabled": False}})]


def test_proof_mining_status_preserves_string_coercion_for_sender_and_hash(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def evaluate_proof_mining_claimability(**kwargs: object) -> _FakeStatus:
        captured.update(kwargs)
        return _FakeStatus({"coerced": True})

    monkeypatch.setattr(
        "src.integration.proof_mining_claimability.evaluate_proof_mining_claimability",
        evaluate_proof_mining_claimability,
    )

    handled = maybe_handle_proof_mining_route(
        path="/api/dex/proof_mining_status",
        obj=_request(tx_sender_pubkey=0, expected_proposal_hash=0),
        write_json=write_json,
    )

    assert handled is True
    assert captured["tx_sender_pubkey"] == "0"
    assert captured["expected_proposal_hash"] == "0"
    assert writes == [(200, {"ok": True, "status": {"coerced": True}})]


def test_proof_mining_status_exception_maps_to_generic_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def evaluate_proof_mining_claimability(**_kwargs: object) -> _FakeStatus:
        raise RuntimeError("claimability failed")

    monkeypatch.setattr(
        "src.integration.proof_mining_claimability.evaluate_proof_mining_claimability",
        evaluate_proof_mining_claimability,
    )

    handled = maybe_handle_proof_mining_route(
        path="/api/dex/proof_mining_status",
        obj=_request(),
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "proof_mining_status_error", "details": "request failed"})]
