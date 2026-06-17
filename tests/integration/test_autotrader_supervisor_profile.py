from __future__ import annotations

import pytest

import src.integration.autotrader_supervisor_profile as supervisor_profile
from src.integration.autotrader_supervisor_profile import (
    AUTOTRADER_SUPERVISOR_EXECUTION_MODE,
    build_autotrader_supervisor_profile_v1,
    evaluate_autotrader_supervisor_profile_v1,
)


def _valid_profile() -> dict[str, object]:
    return build_autotrader_supervisor_profile_v1(
        supervisor_id="supervisor.local.1",
        chain_id="tau-testnet-local",
        stage="public_testnet",
        enabled=True,
        execution_mode=AUTOTRADER_SUPERVISOR_EXECUTION_MODE,
        external_signed_payload_required=True,
        execution_id_required=True,
        release_certificate_required=True,
        stage_certificate_required=True,
        require_testnet_submission=True,
        require_local_preparation=True,
        max_actions_per_tick=4,
        max_runs_per_process=16,
        allowed_templates=["dca"],
        allowed_actions=["PLACE_SWAP_EXACT_IN"],
    )


def test_autotrader_supervisor_profile_accepts_ready_profile() -> None:
    status = evaluate_autotrader_supervisor_profile_v1(
        _valid_profile(),
        expected_chain_id="tau-testnet-local",
    )

    assert status["ok"] is True
    assert status["supervisor_ready"] is True
    assert status["status"] == "ready"
    assert status["readiness_gaps"] == []


def test_autotrader_supervisor_profile_rejects_malformed_input() -> None:
    status = evaluate_autotrader_supervisor_profile_v1("bad")

    assert status["ok"] is False
    assert status["status"] == "blocked"
    assert status["readiness_gaps"] == [
        "autotrader supervisor profile invalid: profile must be a JSON object"
    ]


def test_autotrader_supervisor_profile_rejects_bad_field_types() -> None:
    profile = _valid_profile()
    profile["max_actions_per_tick"] = "bad"
    profile["supervisor_hash"] = supervisor_profile.autotrader_supervisor_profile_hash_v1(profile)

    status = evaluate_autotrader_supervisor_profile_v1(profile)

    assert status["ok"] is False
    assert status["status"] == "blocked"
    assert status["readiness_gaps"] == ["max_actions_per_tick must be a positive int"]


def test_autotrader_supervisor_profile_mapping_adapter_bugs_propagate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def broken_mapping_adapter(_value: object, *, name: str) -> object:
        raise RuntimeError(f"{name} mapping adapter bug")

    monkeypatch.setattr(supervisor_profile, "_require_mapping", broken_mapping_adapter)
    with pytest.raises(RuntimeError, match="profile mapping adapter bug"):
        evaluate_autotrader_supervisor_profile_v1(_valid_profile())


def test_autotrader_supervisor_profile_field_adapter_bugs_propagate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    profile = _valid_profile()

    def broken_string_adapter(_value: object, *, name: str) -> object:
        raise RuntimeError(f"{name} string adapter bug")

    monkeypatch.setattr(supervisor_profile, "_require_nonempty_str", broken_string_adapter)
    with pytest.raises(RuntimeError, match="schema string adapter bug"):
        evaluate_autotrader_supervisor_profile_v1(profile)
