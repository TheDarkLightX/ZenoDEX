"""Promotion-lane tests for the canonical Rust authority surface."""

from __future__ import annotations

import copy
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import AuthorityMode, load_authority_policy, validate_authority_policy  # noqa: E402
from src.runtime.canonical_authority import (  # noqa: E402
    CANONICAL_SURFACE,
    canonical_json_hash_with_authority,
    decide_canonical_cases,
    diff_results,
    locate_runtime_binary,
    py_eval_cases,
)


@pytest.fixture(scope="module")
def rust_bin():
    try:
        return locate_runtime_binary(allow_build=True)
    except Exception as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust runtime unavailable: {exc}")


def _cases() -> list[dict]:
    return [
        {"op": "json_hash", "value": {"b": 2, "a": 1}},
        {
            "op": "domain_json_hash",
            "label": "zenodex.test",
            "version": 1,
            "value": {"asset": "zUSD", "amount": 12_345},
        },
        {"op": "hex_to_bytes", "hex": "0x" + "ab" * 32, "nbytes": 32},
        {"op": "json_bytes", "value": 1.25},
        {"op": "domain_json_hash", "label": "", "version": 1, "value": {}},
        {"op": "hex_to_bytes", "hex": "0xzz", "nbytes": 1},
    ]


def test_public_testnet_profile_promotes_canonical_only():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.default is AuthorityMode.PYTHON_AUTHORITY
    assert policy.mode_for(CANONICAL_SURFACE) is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert policy.promoted_surfaces == frozenset({CANONICAL_SURFACE})
    validate_authority_policy(policy, profile_id="public-testnet")


def test_production_strict_keeps_python_authority():
    profile = load_deploy_profile("production-strict")
    policy = load_authority_policy(profile)

    assert policy.default is AuthorityMode.PYTHON_AUTHORITY
    assert policy.mode_for(CANONICAL_SURFACE) is AuthorityMode.PYTHON_AUTHORITY
    assert policy.promoted_surfaces == frozenset()
    validate_authority_policy(policy, profile_id="production-strict")


def test_public_testnet_canonical_runs_rust_authority_with_python_shadow(rust_bin):
    profile = load_deploy_profile("public-testnet")
    decision = decide_canonical_cases(_cases(), profile=profile, rust_bin=rust_bin)

    assert decision.authority == "rust"
    assert decision.shadow_checked is True
    assert decision.agreed is True
    assert not diff_results(py_eval_cases(_cases()), decision.result)


def test_public_testnet_canonical_rollback_to_python_is_root_preserving(rust_bin):
    promoted = load_deploy_profile("public-testnet")
    rollback = copy.deepcopy(promoted)
    rollback["runtime_authority_policy"]["per_surface"] = {}
    rollback["runtime_authority_policy"]["promoted_surfaces"] = []

    rust_decision = decide_canonical_cases(_cases(), profile=promoted, rust_bin=rust_bin)
    python_decision = decide_canonical_cases(_cases(), profile=rollback, rust_bin=rust_bin)

    assert rust_decision.authority == "rust"
    assert python_decision.authority == "python"
    assert not diff_results(python_decision.result, rust_decision.result)


def test_public_testnet_rejects_half_configured_rust_authority():
    profile = load_deploy_profile("public-testnet")
    broken = copy.deepcopy(profile)
    broken["runtime_authority_policy"]["promoted_surfaces"] = []

    conflicts = evaluate_deploy_profile_consistency(broken, {})

    assert any("half-configured Rust authority" in conflict for conflict in conflicts)


def test_canonical_json_hash_helper_returns_authority_metadata(rust_bin):
    profile = load_deploy_profile("public-testnet")
    digest, metadata = canonical_json_hash_with_authority(
        {"b": 2, "a": 1},
        profile=profile,
        rust_bin=rust_bin,
    )

    assert digest.startswith("0x")
    assert metadata == {
        "surface": "canonical",
        "authority_mode": "rust_authority_with_python_shadow",
        "decided_by": "rust",
        "shadow_checked": True,
        "shadow_agreed": True,
    }
