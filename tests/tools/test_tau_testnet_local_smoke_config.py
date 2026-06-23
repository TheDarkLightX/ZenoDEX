from __future__ import annotations

import pytest

import tools.tau_testnet_local_smoke as smoke


def test_state_proof_bool_env_rejects_malformed_value(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TAU_STATE_PROOF_ALLOW_PATH_LOOKUP", "maybe")

    with pytest.raises(RuntimeError, match="TAU_STATE_PROOF_ALLOW_PATH_LOOKUP"):
        smoke._bool_env("TAU_STATE_PROOF_ALLOW_PATH_LOOKUP", default=False)


def test_state_proof_timeout_rejects_nonfinite_value(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S", "nan")

    with pytest.raises(RuntimeError, match="TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S"):
        smoke._verifier_subprocess_config()


def test_state_proof_output_caps_reject_malformed_values(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TAU_STATE_PROOF_MAX_STDOUT_BYTES", "oops")

    with pytest.raises(RuntimeError, match="TAU_STATE_PROOF_MAX_STDOUT_BYTES"):
        smoke._verifier_subprocess_config()


def test_state_proof_output_caps_reject_out_of_range_values(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TAU_STATE_PROOF_MAX_STDERR_BYTES", "0")

    with pytest.raises(RuntimeError, match="TAU_STATE_PROOF_MAX_STDERR_BYTES"):
        smoke._verifier_subprocess_config()


def test_state_proof_subprocess_config_accepts_explicit_bounds(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S", "2.5")
    monkeypatch.setenv("TAU_STATE_PROOF_MAX_STDOUT_BYTES", "1024")
    monkeypatch.setenv("TAU_STATE_PROOF_MAX_STDERR_BYTES", "512")

    cfg = smoke._verifier_subprocess_config()

    assert cfg.timeout_s == 2.5
    assert cfg.max_stdout_bytes == 1024
    assert cfg.max_stderr_bytes == 512
