from __future__ import annotations

import json


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
AZURE_HOSTDATA = "c" * 64


def test_load_confidential_feature_status_from_env_defaults(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.delenv("CONFIDENTIAL_FEATURE_STAGE", raising=False)
    monkeypatch.delenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", raising=False)
    monkeypatch.delenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", raising=False)

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.stage == "beta"
    assert public["beta_ready"] is False
    assert public["default_enabled"] is False
    assert public["fhe_alpha_enabled"] is False
    assert public["approved_measurements_count"] == 0
    assert "approved measurement allowlist is empty" in public["readiness_gaps"]
    assert "operator contact is missing or placeholder" in public["readiness_gaps"]


def test_load_confidential_feature_status_merges_env_and_file(monkeypatch, tmp_path) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    path = tmp_path / "measurements.json"
    path.write_text(
        json.dumps(
            {
                "approved_measurements": [
                    f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
                    f"azure-sevsnp:hostdata:{AZURE_HOSTDATA}",
                ]
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", str(path))
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}, custom:edge")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "confidential@zenodex.test")
    monkeypatch.setenv("CONFIDENTIAL_FHE_ALPHA_ENABLED", "true")

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.operator_contact == "confidential@zenodex.test"
    assert public["approved_measurements_count"] == 3
    assert public["beta_ready"] is False
    assert public["fhe_alpha_enabled"] is True
    assert "fhe alpha must stay disabled for beta posture" in public["readiness_gaps"]
    assert "cryptographic attestation verification remains external-only" in public["readiness_gaps"]
    assert sorted(public["providers"]) == ["azure-sevsnp", "custom", "nitro"]


def test_load_confidential_feature_status_invalid_stage_falls_back_to_beta(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_FEATURE_STAGE", "ship-it")
    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.stage == "experimental"
    assert public["beta_ready"] is False
    assert "feature stage is experimental, not beta/ga" in public["readiness_gaps"]


def test_load_confidential_feature_status_malformed_bool_fails_closed(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_ENABLED", "maybe")

    try:
        load_confidential_feature_status_from_env()
        assert False, "malformed boolean config must fail closed"
    except ValueError as exc:
        assert "CONFIDENTIAL_SEALED_BID_ENABLED" in str(exc)


def test_load_confidential_feature_status_malformed_int_fails_closed(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_MAX_ATTESTATION_AGE_EPOCHS", "nan")

    try:
        load_confidential_feature_status_from_env()
        assert False, "malformed integer config must fail closed"
    except ValueError as exc:
        assert "CONFIDENTIAL_MAX_ATTESTATION_AGE_EPOCHS" in str(exc)


def test_load_confidential_feature_status_unreadable_measurement_file_fails_closed(monkeypatch, tmp_path) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    path = tmp_path / "measurements.json"
    path.write_text(json.dumps([f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"]), encoding="utf-8")
    path.chmod(0)
    try:
        monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", str(path))
        status = load_confidential_feature_status_from_env()
        public = status.to_public_dict()
        assert public["approved_measurements_count"] == 0
        assert public["beta_ready"] is False
    finally:
        path.chmod(0o600)


def test_confidential_feature_status_helpers_cover_env_and_file_edges(monkeypatch, tmp_path) -> None:
    from src.integration import confidential_feature_status as mod

    monkeypatch.delenv("UNIT_TEST_INT", raising=False)
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 7
    monkeypatch.setenv("UNIT_TEST_INT", " ")
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 7
    monkeypatch.setenv("UNIT_TEST_INT", "oops")
    try:
        mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9)
        assert False, "malformed integer config must fail closed"
    except ValueError as exc:
        assert "UNIT_TEST_INT" in str(exc)
    monkeypatch.setenv("UNIT_TEST_INT", "-5")
    try:
        mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9)
        assert False, "out-of-range integer config must fail closed"
    except ValueError as exc:
        assert "UNIT_TEST_INT" in str(exc)
    monkeypatch.setenv("UNIT_TEST_INT", "15")
    try:
        mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9)
        assert False, "out-of-range integer config must fail closed"
    except ValueError as exc:
        assert "UNIT_TEST_INT" in str(exc)
    monkeypatch.setenv("UNIT_TEST_INT", "5")
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 5

    monkeypatch.delenv("UNIT_TEST_BOOL", raising=False)
    assert mod._env_bool("UNIT_TEST_BOOL", True) is True
    monkeypatch.setenv("UNIT_TEST_BOOL", "off")
    assert mod._env_bool("UNIT_TEST_BOOL", True) is False
    monkeypatch.setenv("UNIT_TEST_BOOL", "maybe")
    try:
        mod._env_bool("UNIT_TEST_BOOL", False)
        assert False, "malformed boolean config must fail closed"
    except ValueError as exc:
        assert "UNIT_TEST_BOOL" in str(exc)

    empty_path = tmp_path / "empty.txt"
    empty_path.write_text("   ", encoding="utf-8")
    assert mod._measurements_from_file(str(empty_path)) == ()

    csv_path = tmp_path / "measurements.csv"
    csv_path.write_text("nitro:a,,custom:x\nazure-sevsnp:y", encoding="utf-8")
    assert mod._measurements_from_file(str(csv_path)) == ("custom:x",)

    list_path = tmp_path / "measurements.json"
    list_path.write_text(json.dumps(["nitro:a", "custom:x", "nitro:a"]), encoding="utf-8")
    assert mod._measurements_from_file(str(list_path)) == ("custom:x",)

    dict_path = tmp_path / "bad-dict.json"
    dict_path.write_text(json.dumps({"approved_measurements": "nitro:a"}), encoding="utf-8")
    assert mod._measurements_from_file(str(dict_path)) == ()

    assert mod._has_real_operator_contact("") is False
    assert mod._has_real_operator_contact("ops@example.invalid") is False
    assert mod._has_real_operator_contact("https://status.zenodex.test") is True


def test_confidential_feature_status_reports_runtime_gaps_even_when_env_requirements_hold(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_FEATURE_STAGE", "ga")
    monkeypatch.setenv("CONFIDENTIAL_TEE_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_DEFAULT", "true")
    monkeypatch.setenv("CONFIDENTIAL_FHE_ALPHA_ENABLED", "false")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "https://ops.zenodex.test")
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}")

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()

    assert public["default_enabled"] is False
    assert public["beta_ready"] is False
    assert "cryptographic attestation verification remains external-only" in public["readiness_gaps"]
    assert "confidential runtime privacy remains external to the live API path" in public["readiness_gaps"]
    assert "confidential execution runtime admission is not wired on the live API path" not in public["readiness_gaps"]
    assert "replay-safe request nonce reservation is not enforced by a local verifier boundary" not in public["readiness_gaps"]
    assert "sealed-bid asset settlement remains external to the local/testnet API path" in public["readiness_gaps"]
    assert "bounded runtime receipts" in public["claim_scope"]
