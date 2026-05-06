from __future__ import annotations

import yaml


def test_claims_registry_is_valid() -> None:
    from tools.check_claims_registry import validate_registry, REGISTRY_PATH

    validate_registry(REGISTRY_PATH)


def test_zeno_oracle_devnet_alpha_claim_tracks_package_replay_gate() -> None:
    from tools.check_claims_registry import REGISTRY_PATH

    registry = yaml.safe_load(REGISTRY_PATH.read_text(encoding="utf-8"))
    claims = {claim["id"]: claim for claim in registry["claims"]}
    claim = claims["py:zeno_oracle:devnet_alpha_replay_gate"]
    evidence = claim["evidence"]
    commands = [row["cmd"] for row in evidence["check"]]
    files = set(evidence["files"])

    assert (
        "cd dist/zeno-oracle-devnet-alpha-rc1 && bash scripts/check_zeno_oracle_rc_bundle.sh"
        in commands
    )
    assert "scripts/check_zeno_oracle_rc_bundle.sh" in files
    assert ".github/workflows/zeno-oracle-mvp.yml" in files
    assert "tools/check_zeno_oracle_frontier_obligation_projection.py" in files


def test_zeno_oracle_compositional_disaster_claim_tracks_public_projection() -> None:
    from tools.check_claims_registry import REGISTRY_PATH

    registry = yaml.safe_load(REGISTRY_PATH.read_text(encoding="utf-8"))
    claims = {claim["id"]: claim for claim in registry["claims"]}
    claim = claims["py:zeno_oracle:compositional_disaster_regression_projection_v1"]
    evidence = claim["evidence"]
    commands = [row["cmd"] for row in evidence["check"]]
    files = set(evidence["files"])

    assert (
        "python3 tools/check_zeno_oracle_compositional_disaster_regressions.py --format text"
        in commands
    )
    assert "tools/zeno_oracle_compositional_disaster_regression_manifest.json" in files
    assert "tests/core/test_perp_submission_auth_gate.py" in files
