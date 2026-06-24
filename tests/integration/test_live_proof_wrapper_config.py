from __future__ import annotations

import json

import pytest


def test_live_zk_proof_required_rejects_malformed_global_flag(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    monkeypatch.setenv("TAU_DEX_REQUIRE_LIVE_ZK_PROOF", "maybe")

    with pytest.raises(ValueError, match="TAU_DEX_REQUIRE_LIVE_ZK_PROOF"):
        live_proof_wrapper.live_zk_proof_required(env_prefix="PERPS_WALLET")


def test_live_zk_proof_required_rejects_malformed_surface_flag(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    monkeypatch.setenv("TAU_DEX_REQUIRE_LIVE_ZK_PROOF", "1")
    monkeypatch.setenv("PERPS_WALLET_REQUIRE_ZK_PROOF", "maybe")

    with pytest.raises(ValueError, match="PERPS_WALLET_REQUIRE_ZK_PROOF"):
        live_proof_wrapper.live_zk_proof_required(env_prefix="PERPS_WALLET")


def test_proof_verifier_config_rejects_malformed_numeric_limits(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(["/bin/true"]))
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_TIMEOUT_S", "nan")
    with pytest.raises(ValueError, match="TAU_DEX_PROOF_VERIFIER_TIMEOUT_S"):
        live_proof_wrapper.proof_verifier_config_from_env(env_prefix="PERPS_WALLET")

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_TIMEOUT_S", "10")
    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_MAX_PROOF_BYTES", "512")
    with pytest.raises(ValueError, match="TAU_DEX_PROOF_VERIFIER_MAX_PROOF_BYTES"):
        live_proof_wrapper.proof_verifier_config_from_env(env_prefix="PERPS_WALLET")


def test_proof_verifier_config_rejects_malformed_command_json_with_env_name(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    monkeypatch.setenv("PERPS_WALLET_PROOF_VERIFIER_CMD_JSON", "not-json")

    with pytest.raises(ValueError, match="PERPS_WALLET_PROOF_VERIFIER_CMD_JSON must be valid JSON"):
        live_proof_wrapper.proof_verifier_config_from_env(env_prefix="PERPS_WALLET")


def test_live_proof_wrapper_caps_json_loader_error_details(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    long_detail = "x" * 300

    with monkeypatch.context() as m:
        m.setenv("TEST_ARTIFACT_JSON", "{")
        m.setattr(
            live_proof_wrapper.json,
            "loads",
            lambda raw: (_ for _ in ()).throw(json.JSONDecodeError(long_detail, "doc", 0)),
        )
        artifact, err = live_proof_wrapper._load_json_object_from_env(
            json_names=("TEST_ARTIFACT_JSON",),
            file_names=(),
            label="test artifact",
        )
        assert artifact is None
        assert err == "test artifact JSON invalid: " + ("x" * 200)

    with monkeypatch.context() as m:
        m.setenv("TEST_ARTIFACT_FILE", "/tmp/missing-artifact.json")
        m.setattr(
            live_proof_wrapper.Path,
            "read_text",
            lambda self, *, encoding: (_ for _ in ()).throw(OSError(long_detail)),
        )
        artifact, err = live_proof_wrapper._load_json_object_from_env(
            json_names=(),
            file_names=("TEST_ARTIFACT_FILE",),
            label="test artifact",
        )
        assert artifact is None
        assert err == "test artifact file unreadable: " + ("x" * 200)

    with monkeypatch.context() as m:
        m.setenv("TEST_ARTIFACT_FILE", "/tmp/bad-artifact.json")
        m.setattr(live_proof_wrapper.Path, "read_text", lambda self, *, encoding: "{")
        m.setattr(
            live_proof_wrapper.json,
            "loads",
            lambda raw: (_ for _ in ()).throw(json.JSONDecodeError(long_detail, "doc", 0)),
        )
        artifact, err = live_proof_wrapper._load_json_object_from_env(
            json_names=(),
            file_names=("TEST_ARTIFACT_FILE",),
            label="test artifact",
        )
        assert artifact is None
        assert err == "test artifact file JSON invalid: " + ("x" * 200)


def test_proof_verifier_config_rejects_malformed_allow_path_lookup(monkeypatch) -> None:
    from src.integration import live_proof_wrapper

    monkeypatch.setenv("TAU_DEX_PROOF_VERIFIER_CMD_JSON", json.dumps(["/bin/true"]))
    monkeypatch.setenv("PERPS_WALLET_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", "maybe")

    with pytest.raises(ValueError, match="PERPS_WALLET_PROOF_VERIFIER_ALLOW_PATH_LOOKUP"):
        live_proof_wrapper.proof_verifier_config_from_env(env_prefix="PERPS_WALLET")
