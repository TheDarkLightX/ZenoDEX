from __future__ import annotations

import json


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
    path.write_text(json.dumps({"approved_measurements": ["nitro:pcr0:aa:pcr8:bb", "azure-sevsnp:hostdata:cc"]}), encoding="utf-8")
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS_FILE", str(path))
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", "nitro:pcr0:aa:pcr8:bb, custom:edge")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "confidential@zenodex.test")
    monkeypatch.setenv("CONFIDENTIAL_FHE_ALPHA_ENABLED", "true")

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.operator_contact == "confidential@zenodex.test"
    assert public["approved_measurements_count"] == 3
    assert public["beta_ready"] is False
    assert public["fhe_alpha_enabled"] is True
    assert public["readiness_gaps"] == ["fhe alpha must stay disabled for beta posture"]
    assert sorted(public["providers"]) == ["azure-sevsnp", "custom", "nitro"]


def test_load_confidential_feature_status_invalid_stage_falls_back_to_beta(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_FEATURE_STAGE", "ship-it")
    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()
    assert status.stage == "experimental"
    assert public["beta_ready"] is False
    assert "feature stage is experimental, not beta/ga" in public["readiness_gaps"]


def test_load_confidential_feature_status_unreadable_measurement_file_fails_closed(monkeypatch, tmp_path) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    path = tmp_path / "measurements.json"
    path.write_text('["nitro:pcr0:aa:pcr8:bb"]', encoding="utf-8")
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
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 7
    monkeypatch.setenv("UNIT_TEST_INT", "-5")
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 1
    monkeypatch.setenv("UNIT_TEST_INT", "15")
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 9
    monkeypatch.setenv("UNIT_TEST_INT", "5")
    assert mod._env_int("UNIT_TEST_INT", 7, lo=1, hi=9) == 5

    empty_path = tmp_path / "empty.txt"
    empty_path.write_text("   ", encoding="utf-8")
    assert mod._measurements_from_file(str(empty_path)) == ()

    csv_path = tmp_path / "measurements.csv"
    csv_path.write_text("nitro:a,,custom:x\nazure-sevsnp:y", encoding="utf-8")
    assert mod._measurements_from_file(str(csv_path)) == ("azure-sevsnp:y", "custom:x", "nitro:a")

    list_path = tmp_path / "measurements.json"
    list_path.write_text(json.dumps(["nitro:a", "custom:x", "nitro:a"]), encoding="utf-8")
    assert mod._measurements_from_file(str(list_path)) == ("custom:x", "nitro:a")

    dict_path = tmp_path / "bad-dict.json"
    dict_path.write_text(json.dumps({"approved_measurements": "nitro:a"}), encoding="utf-8")
    assert mod._measurements_from_file(str(dict_path)) == ('{"approved_measurements": "nitro:a"}',)

    assert mod._has_real_operator_contact("") is False
    assert mod._has_real_operator_contact("ops@example.invalid") is False
    assert mod._has_real_operator_contact("https://status.zenodex.test") is True


def test_confidential_feature_status_reports_beta_ready_when_all_requirements_hold(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_FEATURE_STAGE", "ga")
    monkeypatch.setenv("CONFIDENTIAL_TEE_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_ENABLED", "true")
    monkeypatch.setenv("CONFIDENTIAL_SEALED_BID_DEFAULT", "true")
    monkeypatch.setenv("CONFIDENTIAL_FHE_ALPHA_ENABLED", "false")
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "https://ops.zenodex.test")
    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", "nitro:pcr0:aa")

    status = load_confidential_feature_status_from_env()
    public = status.to_public_dict()

    assert public["default_enabled"] is True
    assert public["beta_ready"] is True
    assert public["readiness_gaps"] == []
