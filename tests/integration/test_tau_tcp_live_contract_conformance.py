from __future__ import annotations

import os

import pytest

import src.integration.tau_net_client as tau_net_client


def _env_flag(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1", "true", "yes", "on"}


def _require_live_tau() -> None:
    if not _env_flag("ZENODEX_TAU_LIVE_CONFORMANCE"):
        pytest.skip("set ZENODEX_TAU_LIVE_CONFORMANCE=1 to run live Tau node conformance checks")


def _live_client() -> tau_net_client.TauNetTcpClient:
    host = os.getenv("ZENODEX_TAU_HOST", "127.0.0.1")
    port = int(os.getenv("ZENODEX_TAU_PORT", "65432"))
    timeout_s = float(os.getenv("ZENODEX_TAU_TIMEOUT_S", "3.0"))
    return tau_net_client.TauNetTcpClient(
        tau_net_client.TauNetTcpConfig(
            host=host,
            port=port,
            timeout_s=timeout_s,
        )
    )


def test_live_tau_node_appstate_and_stateproof_conformance() -> None:
    _require_live_tau()
    client = _live_client()

    app_state_view = client.getappstate_view()
    state_proof_view = client.getstateproof_view()

    assert isinstance(app_state_view, tau_net_client.TauNetAppStateView)
    assert isinstance(state_proof_view, tau_net_client.TauNetStateProofView)
    assert isinstance(app_state_view.app_hash, str)
    assert len(app_state_view.app_hash) in {0, 64}
    assert isinstance(state_proof_view.present, bool)
    assert len(state_proof_view.state_hash) in {0, 64}


def test_live_tau_node_gettaustate_conformance_when_requested() -> None:
    _require_live_tau()
    if not _env_flag("ZENODEX_TAU_LIVE_REQUIRE_GETTAUSTATE"):
        pytest.skip("set ZENODEX_TAU_LIVE_REQUIRE_GETTAUSTATE=1 to require live gettaustate conformance")

    client = _live_client()
    state_proof_view = client.getstateproof_view()
    assert state_proof_view.present is True
    assert len(state_proof_view.state_hash) == 64

    tau_state_view = client.gettaustate_view(state_proof_view.state_hash)
    assert isinstance(tau_state_view, tau_net_client.TauNetTauStateView)
    assert tau_state_view.state_hash == state_proof_view.state_hash
    assert isinstance(tau_state_view.rules, str)
    assert len(tau_state_view.accounts_hash) == 64
    assert len(tau_state_view.app_hash) in {0, 64}
