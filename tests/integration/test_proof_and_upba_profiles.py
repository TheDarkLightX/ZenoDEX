from __future__ import annotations

import copy
import json
from pathlib import Path

from tools.check_upba_policy_profiles import validate_upba_policy_dir_v1, validate_upba_policy_profile_v1
from tools.check_zeno_ledger_proof_profiles import validate_proof_profiles_v1


def test_zeno_ledger_proof_profiles_accept_default_registry() -> None:
    registry = json.loads(Path("config/proof_profiles/zeno_ledger_profiles.json").read_text(encoding="utf-8"))
    report = validate_proof_profiles_v1(registry)

    assert report["ok"] is True
    assert report["profile_count"] == 4


def test_zeno_ledger_proof_profiles_reject_hash_mismatch() -> None:
    registry = json.loads(Path("config/proof_profiles/zeno_ledger_profiles.json").read_text(encoding="utf-8"))
    registry["coverage_matrix_sha256"] = "0" * 64

    report = validate_proof_profiles_v1(registry)

    assert report["ok"] is False
    assert "coverage_matrix_sha256 mismatch" in report["errors"]


def test_upba_policy_profiles_accept_default_dir() -> None:
    report = validate_upba_policy_dir_v1(Path("config/upba"))

    assert report["ok"] is True
    assert [item["profile_id"] for item in report["profiles"]] == ["conservative", "balanced", "fast"]


def test_upba_policy_rejects_energy_candidate_omission_without_certificate() -> None:
    profile = json.loads(Path("config/upba/policy_balanced.json").read_text(encoding="utf-8"))
    bad = copy.deepcopy(profile)
    bad["energy_may_omit_candidates"] = True
    bad["energy_omit_requires_certificate"] = False

    report = validate_upba_policy_profile_v1(bad)

    assert report["ok"] is False
    assert "energy omission requires deterministic suffix-bound or selected-set certificate" in report["errors"]
    assert "default ZenoEnergy policy must be order-only" in report["errors"]
