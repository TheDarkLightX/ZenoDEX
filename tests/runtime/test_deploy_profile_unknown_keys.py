"""Regression (F-2): load_deploy_profile rejects unknown top-level keys.

A mistyped policy block (e.g. ``runtime_polciy`` instead of ``runtime_policy``)
previously passed ``load_deploy_profile`` — only the ``schema`` was checked — and
then degraded to ``{}`` inside ``evaluate_deploy_profile_consistency``, silently
disabling the matching runtime conflict check (fail open). The loader must reject
any unknown top-level key at load time (fail closed) so an intended restriction
cannot become a no-op through a typo.
"""

from __future__ import annotations

import pytest
import yaml

from src.integration.deploy_profile import load_deploy_profile


def test_shipped_profiles_still_load():
    # The three shipped profiles use only allowlisted top-level keys.
    for profile_id in ("local-dev", "public-testnet", "production-strict"):
        profile = load_deploy_profile(profile_id)
        assert profile["profile_id"] == profile_id


def test_unknown_top_level_key_rejected(tmp_path, monkeypatch):
    # Faithful copy of production-strict with the runtime_policy block name typo'd.
    # Deploy profile loading is allowlisted by profile id (no arbitrary paths),
    # so we monkeypatch the deploy dir and allowlist to admit a test profile.
    base = load_deploy_profile("production-strict")
    base["runtime_polciy"] = base.pop("runtime_policy")
    base["profile_id"] = "test-typo"
    path = tmp_path / "test-typo.yaml"
    path.write_text(yaml.safe_dump(base), encoding="utf-8")
    import src.integration.deploy_profile as dp
    monkeypatch.setattr(dp, "_DEPLOY_DIR", tmp_path)
    monkeypatch.setattr(dp, "_DEPLOY_PROFILE_IDS", frozenset({"test-typo"}))
    with pytest.raises(ValueError, match="unknown top-level keys"):
        load_deploy_profile("test-typo")


def test_extra_unknown_key_rejected(tmp_path, monkeypatch):
    base = load_deploy_profile("public-testnet")
    base["bogus_extra_policy"] = {"enabled": True}
    base["profile_id"] = "test-extra"
    path = tmp_path / "test-extra.yaml"
    path.write_text(yaml.safe_dump(base), encoding="utf-8")
    import src.integration.deploy_profile as dp
    monkeypatch.setattr(dp, "_DEPLOY_DIR", tmp_path)
    monkeypatch.setattr(dp, "_DEPLOY_PROFILE_IDS", frozenset({"test-extra"}))
    with pytest.raises(ValueError, match="bogus_extra_policy"):
        load_deploy_profile("test-extra")


def test_arbitrary_filesystem_path_rejected(tmp_path):
    # Path hardening: load_deploy_profile must reject arbitrary filesystem
    # paths and only accept allowlisted profile ids.
    path = tmp_path / "evil.yaml"
    path.write_text("schema: zenodex/deployment_profile/v1\nprofile_id: evil\n", encoding="utf-8")
    with pytest.raises(ValueError, match="invalid deploy profile id"):
        load_deploy_profile(str(path))


def test_static_validator_also_rejects_unknown_keys():
    # The CI gate (tools/check_deployment_profiles.validate_deployment_profile)
    # must share the runtime loader's fail-closed contract so it cannot pass a
    # profile the runtime would refuse.
    from tools.check_deployment_profiles import validate_deployment_profile

    good = load_deploy_profile("production-strict")
    assert validate_deployment_profile(dict(good))["ok"] is True

    typo = dict(good)
    typo["runtime_polciy"] = typo.pop("runtime_policy")
    report = validate_deployment_profile(typo)
    assert report["ok"] is False
    assert any("unknown top-level keys" in e for e in report["errors"])
