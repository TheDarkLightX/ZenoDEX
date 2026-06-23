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
    spot_v1 = next(profile for profile in registry["profiles"] if profile["profile_id"] == "spot_v1_single_pool_success")
    assert "swap_exact_in" in spot_v1["covered"]
    assert "swap_exact_out" not in spot_v1["covered"]
    assert "swap_exact_out" in spot_v1["not_covered"]
    assert "does_not_claim_spot_v1_exact_out_zk_execution" in spot_v1["non_claims"]


def test_zeno_ledger_proof_profiles_reject_spot_v1_exact_out_overclaim() -> None:
    registry = json.loads(Path("config/proof_profiles/zeno_ledger_profiles.json").read_text(encoding="utf-8"))
    bad = copy.deepcopy(registry)
    spot_v1 = next(profile for profile in bad["profiles"] if profile["profile_id"] == "spot_v1_single_pool_success")
    spot_v1["covered"].append("swap_exact_out")
    spot_v1["not_covered"] = [item for item in spot_v1["not_covered"] if item != "swap_exact_out"]

    report = validate_proof_profiles_v1(bad)

    assert report["ok"] is False
    assert any("forbidden coverage: swap_exact_out" in error for error in report["errors"])


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
