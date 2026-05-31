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


def test_unknown_top_level_key_rejected(tmp_path):
    # Faithful copy of production-strict with the runtime_policy block name typo'd.
    base = load_deploy_profile("production-strict")
    base["runtime_polciy"] = base.pop("runtime_policy")
    path = tmp_path / "typo-profile.yaml"
    path.write_text(yaml.safe_dump(base), encoding="utf-8")
    with pytest.raises(ValueError, match="unknown top-level keys"):
        load_deploy_profile(str(path))


def test_extra_unknown_key_rejected(tmp_path):
    base = load_deploy_profile("public-testnet")
    base["bogus_extra_policy"] = {"enabled": True}
    path = tmp_path / "extra-key-profile.yaml"
    path.write_text(yaml.safe_dump(base), encoding="utf-8")
    with pytest.raises(ValueError, match="bogus_extra_policy"):
        load_deploy_profile(str(path))
