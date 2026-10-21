"""Authority-demotion and shadow parity tests for canonical encoding."""

from __future__ import annotations

import copy
import json
import sys
from types import SimpleNamespace
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import AuthorityMode, load_authority_policy, validate_authority_policy  # noqa: E402
from src.runtime.canonical_authority import (  # noqa: E402
    CANONICAL_SURFACE,
    CanonicalAuthorityError,
    canonical_json_hash_with_authority,
    decide_canonical_cases,
    diff_results,
    locate_runtime_binary,
    py_eval_cases,
    rust_eval_cases,
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


def _patch_rust_stdout(monkeypatch, payload: dict) -> None:
    def fake_run(*_args, **_kwargs):
        return SimpleNamespace(returncode=0, stdout=json.dumps(payload), stderr="")

    from src.runtime import canonical_authority

    monkeypatch.setattr(canonical_authority.subprocess, "run", fake_run)


def test_public_testnet_profile_demotes_partial_cbc_canonical():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.default is AuthorityMode.PYTHON_AUTHORITY
    assert policy.mode_for(CANONICAL_SURFACE) is AuthorityMode.PYTHON_AUTHORITY
    assert CANONICAL_SURFACE not in policy.promoted_surfaces
    validate_authority_policy(policy, profile_id="public-testnet")


def test_production_strict_keeps_python_authority():
    profile = load_deploy_profile("production-strict")
    policy = load_authority_policy(profile)

    assert policy.default is AuthorityMode.PYTHON_AUTHORITY
    assert policy.mode_for(CANONICAL_SURFACE) is AuthorityMode.PYTHON_AUTHORITY
    assert policy.promoted_surfaces == frozenset()
    validate_authority_policy(policy, profile_id="production-strict")


def test_public_testnet_canonical_uses_python_authority(rust_bin):
    profile = load_deploy_profile("public-testnet")
    decision = decide_canonical_cases(_cases(), profile=profile, rust_bin=rust_bin)

    assert decision.authority == "python"
    assert decision.shadow_checked is False
    assert decision.agreed is None
    assert not diff_results(py_eval_cases(_cases()), decision.result)


def test_public_testnet_canonical_python_fallback_is_root_preserving(rust_bin):
    demoted = load_deploy_profile("public-testnet")
    rollback = copy.deepcopy(demoted)
    rollback["runtime_authority_policy"]["per_surface"] = {}
    rollback["runtime_authority_policy"]["promoted_surfaces"] = []

    current_decision = decide_canonical_cases(
        _cases(), profile=demoted, rust_bin=rust_bin
    )
    python_decision = decide_canonical_cases(_cases(), profile=rollback, rust_bin=rust_bin)

    assert current_decision.authority == "python"
    assert python_decision.authority == "python"
    assert not diff_results(python_decision.result, current_decision.result)


def test_public_testnet_rejects_half_configured_rust_authority():
    profile = load_deploy_profile("public-testnet")
    broken = copy.deepcopy(profile)
    broken["runtime_authority_policy"]["per_surface"] = dict(
        profile["runtime_authority_policy"]["per_surface"]
    )
    broken["runtime_authority_policy"]["per_surface"][CANONICAL_SURFACE] = (
        "rust_authority_with_python_shadow"
    )

    conflicts = evaluate_deploy_profile_consistency(broken, {})

    assert any(
        CANONICAL_SURFACE in conflict and "partial-CBC surfaces" in conflict
        for conflict in conflicts
    )


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
        "authority_mode": "python_authority",
        "decided_by": "python",
        "shadow_checked": False,
        "shadow_agreed": None,
    }


def test_canonical_rust_eval_rejects_extra_top_level_field(monkeypatch):
    _patch_rust_stdout(
        monkeypatch,
        {
            "version": 1,
            "results": [{"index": 0, "ok": False, "code": "bad_json_number"}],
            "extra": "metadata",
        },
    )

    with pytest.raises(CanonicalAuthorityError, match="rust canonical output: unexpected fields"):
        rust_eval_cases([{"op": "json_hash", "value": 1.25}], rust_bin=Path("/tmp/fake-runtime"))


def test_canonical_rust_eval_rejects_extra_result_field(monkeypatch):
    _patch_rust_stdout(
        monkeypatch,
        {
            "version": 1,
            "results": [
                {"index": 0, "ok": True, "bytes": "0x7b7d", "hash": "0x00", "extra": "metadata"}
            ],
        },
    )

    with pytest.raises(CanonicalAuthorityError, match="rust canonical result 0: unexpected fields"):
        rust_eval_cases([{"op": "json_hash", "value": {}}], rust_bin=Path("/tmp/fake-runtime"))


def test_canonical_rust_eval_rejects_non_bool_ok(monkeypatch):
    _patch_rust_stdout(
        monkeypatch,
        {"version": 1, "results": [{"index": 0, "ok": 1, "bytes": "0x7b7d", "hash": "0x00"}]},
    )

    with pytest.raises(CanonicalAuthorityError, match="rust canonical result 0 ok must be a bool"):
        rust_eval_cases([{"op": "json_hash", "value": {}}], rust_bin=Path("/tmp/fake-runtime"))


def test_canonical_rust_eval_rejects_index_mismatch(monkeypatch):
    _patch_rust_stdout(
        monkeypatch,
        {"version": 1, "results": [{"index": 1, "ok": True, "hash": "0x00"}]},
    )

    with pytest.raises(CanonicalAuthorityError, match="rust canonical result 0 index mismatch"):
        rust_eval_cases(
            [{"op": "domain_json_hash", "label": "zenodex.test", "version": 1, "value": {}}],
            rust_bin=Path("/tmp/fake-runtime"),
        )


def test_canonical_diff_results_rejects_malformed_ok_and_index():
    assert diff_results([{"index": 0, "ok": True}], [{"index": 0, "ok": 1}]) == [
        "case 0: malformed ok left=True right=1"
    ]
    assert diff_results([{"index": 0, "ok": True}], [{"index": 1, "ok": True}]) == [
        "case 0: index left=0 right=1"
    ]
