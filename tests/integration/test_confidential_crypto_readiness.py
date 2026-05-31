from __future__ import annotations


MEASUREMENT = "nitro:pcr0:" + ("a" * 96) + ":pcr8:" + ("b" * 96)


def _confidential_status(**overrides):
    body = {
        "tee_enabled": True,
        "approved_measurements_count": 1,
        "approved_measurements_hash": "0x" + "11" * 32,
        "fhe_alpha_enabled": False,
    }
    body.update(overrides)
    return body


def _attestation_status(**overrides):
    body = {
        "external_verifier_enabled": True,
        "external_verifier_configured": True,
        "external_verifier_binding_hash": "0x" + "22" * 32,
    }
    body.update(overrides)
    return body


def _sss_status(**overrides):
    body = {
        "sss_implemented": True,
        "encrypted_sss_backup_ready": True,
        "external_audit_ready": True,
        "live_provider_delivery_ready": True,
        "replay_recovery_ready": True,
        "replay_hostile_tests_ready": True,
        "hostile_share_tests_ready": True,
        "raw_material_absent": True,
        "server_side_reconstitution": False,
    }
    body.update(overrides)
    return body


def _surface(report, surface_id):
    return next(surface for surface in report["surfaces"] if surface["id"] == surface_id)


def test_confidential_crypto_readiness_blocks_external_only_tee_and_missing_surfaces() -> None:
    from src.integration.confidential_crypto_readiness import build_confidential_crypto_readiness_v1

    report = build_confidential_crypto_readiness_v1(
        confidential_status=_confidential_status(),
        attestation_status=_attestation_status(),
    )

    assert report["production_ready"] is False
    assert report["host_independent_ready"] is False
    assert str(report["readiness_hash"]).startswith("0x")
    tee = _surface(report, "tee_attestation")
    assert tee["state"] == "external-verifier-bound"
    assert tee["production_ready"] is False
    assert "vendor attestation verifier semantics remain external to this repo" in tee["readiness_gaps"]
    assert _surface(report, "sss_backup")["state"] == "missing"
    assert _surface(report, "mpc")["state"] == "missing"
    assert _surface(report, "fhe")["state"] == "alpha-disabled"


def test_confidential_crypto_readiness_recognizes_audited_sss_candidate_but_keeps_overall_blocked() -> None:
    from src.integration.confidential_crypto_readiness import build_confidential_crypto_readiness_v1

    report = build_confidential_crypto_readiness_v1(
        confidential_status=_confidential_status(),
        attestation_status=_attestation_status(),
        encrypted_sss_backup_status=_sss_status(),
    )

    sss = _surface(report, "sss_backup")
    assert sss["production_ready"] is True
    assert sss["host_independent_ready"] is True
    assert sss["readiness_gaps"] == []
    assert report["production_ready"] is False
    assert any(gap.startswith("tee_attestation:") for gap in report["readiness_gaps"])
    assert any(gap.startswith("mpc:") for gap in report["readiness_gaps"])
    assert any(gap.startswith("fhe:") for gap in report["readiness_gaps"])


def test_confidential_crypto_readiness_classifies_placeholder_mpc_backend() -> None:
    from src.integration.confidential_crypto_readiness import build_confidential_crypto_readiness_v1

    report = build_confidential_crypto_readiness_v1(
        confidential_status=_confidential_status(),
        attestation_status=_attestation_status(),
        encrypted_sss_backup_status=_sss_status(),
        key_backend_descriptors=(
            {
                "backend_kind": "mpc-placeholder",
                "backend_id": "wallet-mpc-placeholder",
            },
        ),
    )

    mpc = _surface(report, "mpc")
    assert mpc["state"] == "placeholder-only"
    assert mpc["implemented"] is False
    assert "MPC backend is still a placeholder" in mpc["readiness_gaps"]


def test_confidential_feature_status_embeds_crypto_readiness(monkeypatch) -> None:
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env

    monkeypatch.setenv("CONFIDENTIAL_APPROVED_MEASUREMENTS", MEASUREMENT)
    monkeypatch.setenv("CONFIDENTIAL_OPERATOR_CONTACT", "https://ops.zenodex.test")
    public = load_confidential_feature_status_from_env().to_public_dict()

    readiness = public["crypto_readiness"]
    assert readiness["schema"] == "zenodex/confidential-crypto-readiness/v1"
    assert readiness["production_ready"] is False
    assert _surface(readiness, "tee_attestation")["state"] == "external-verifier-missing"


def test_missing_encrypted_sss_status_reports_readiness_blocker() -> None:
    from src.integration.confidential_crypto_readiness import build_confidential_crypto_readiness_v1

    report = build_confidential_crypto_readiness_v1(
        confidential_status=_confidential_status(),
        attestation_status=_attestation_status(),
    )
    sss = _surface(report, "sss_backup")

    assert sss["state"] == "missing"
    assert sss["implemented"] is False
    assert sss["production_ready"] is False
    assert "encrypted SSS backup status is missing" in sss["readiness_gaps"]
