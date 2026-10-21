"""Tests for the runtime authority selector (Phase 2).

Proves the four required properties from the promotion prompt:
  * unsupported authority mode rejects;
  * strict public-testnet / production profiles cannot enable half-configured Rust authority;
  * disagreement between Rust and Python fails closed;
  * state roots are unchanged across python_authority and
    rust_authority_with_python_shadow for promoted (agreeing) surfaces;
plus the full mode semantics and fail-closed paths.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.runtime.authority import (  # noqa: E402
    DEFAULT_MODE,
    AuthorityDecision,
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES,
    RustUnavailable,
    active_mode,
    decide,
    load_authority_policy,
    parse_authority_mode,
    reset_active_authority_policy,
    set_active_authority_policy,
    validate_authority_policy,
)


# A canonical "result" mirrors what a real surface returns: a receipt hash and
# a post-state-root contribution. Equality of these is the agreement check and
# the state-root-unchanged property.
PY_RESULT = {"receipt_hash": "0xpy", "post_state_root": "0xroot", "accepted": True}
RUST_SAME = {"receipt_hash": "0xpy", "post_state_root": "0xroot", "accepted": True}
RUST_DIFFERENT = {"receipt_hash": "0xru", "post_state_root": "0xDIFF", "accepted": True}


class _Counter:
    """A zero-arg callable that returns a fixed value and counts calls."""

    def __init__(self, value):
        self.value = value
        self.calls = 0

    def __call__(self):
        self.calls += 1
        return self.value


def _boom():
    raise AssertionError("this engine must not be called")


# --------------------------------------------------------------------------
# Mode parsing
# --------------------------------------------------------------------------

def test_parse_rejects_unsupported_mode():
    with pytest.raises(ValueError):
        parse_authority_mode("nonsense_mode")
    with pytest.raises(ValueError):
        parse_authority_mode(123)


def test_parse_accepts_all_valid_modes():
    for mode in AuthorityMode:
        assert parse_authority_mode(mode.value) is mode
        assert parse_authority_mode(mode) is mode


def test_default_mode_is_python():
    assert DEFAULT_MODE is AuthorityMode.PYTHON_AUTHORITY
    policy = load_authority_policy(None)
    assert policy.mode_for("any_surface") is AuthorityMode.PYTHON_AUTHORITY


def test_active_policy_defaults_and_resets():
    reset_active_authority_policy()
    assert active_mode("canonical") is AuthorityMode.PYTHON_AUTHORITY
    set_active_authority_policy(
        AuthorityPolicy(
            default=AuthorityMode.PYTHON_AUTHORITY,
            per_surface={"canonical": AuthorityMode.RUST_SHADOW},
            promoted_surfaces=frozenset(),
        )
    )
    assert active_mode("canonical") is AuthorityMode.RUST_SHADOW
    reset_active_authority_policy()
    assert active_mode("canonical") is AuthorityMode.PYTHON_AUTHORITY


# --------------------------------------------------------------------------
# python_authority
# --------------------------------------------------------------------------

def test_python_authority_runs_only_python():
    py = _Counter(PY_RESULT)
    d = decide("fee_router", AuthorityMode.PYTHON_AUTHORITY, python_fn=py, rust_fn=_boom)
    assert d.authority == "python"
    assert d.result == PY_RESULT
    assert d.shadow_checked is False
    assert d.agreed is None
    assert py.calls == 1  # rust_fn (_boom) never called


# --------------------------------------------------------------------------
# rust_shadow (Python authority, Rust checks)
# --------------------------------------------------------------------------

def test_rust_shadow_agreement_keeps_python_authority():
    py, ru = _Counter(PY_RESULT), _Counter(RUST_SAME)
    d = decide("fee_router", AuthorityMode.RUST_SHADOW, python_fn=py, rust_fn=ru)
    assert d.authority == "python"
    assert d.result == PY_RESULT
    assert d.shadow_checked is True
    assert d.agreed is True
    assert py.calls == 1 and ru.calls == 1


def test_rust_shadow_disagreement_fails_closed():
    py, ru = _Counter(PY_RESULT), _Counter(RUST_DIFFERENT)
    with pytest.raises(AuthorityError):
        decide("fee_router", AuthorityMode.RUST_SHADOW, python_fn=py, rust_fn=ru)


def test_rust_shadow_rejects_none_none_default_agreement():
    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_SHADOW,
            python_fn=_Counter(None),
            rust_fn=_Counter(None),
        )


def test_rust_shadow_unavailable_is_skipped():
    def rust_unavailable():
        raise RustUnavailable("not built")

    py = _Counter(PY_RESULT)
    d = decide("fee_router", AuthorityMode.RUST_SHADOW, python_fn=py, rust_fn=rust_unavailable)
    assert d.authority == "python"
    assert d.shadow_checked is False
    assert d.agreed is None


def test_rust_shadow_error_fails_closed():
    def rust_malformed():
        raise ValueError("malformed rust output")

    with pytest.raises(AuthorityError):
        decide("fee_router", AuthorityMode.RUST_SHADOW, python_fn=_Counter(PY_RESULT), rust_fn=rust_malformed)


def test_rust_shadow_without_rust_fn_runs_python_only():
    py = _Counter(PY_RESULT)
    d = decide("fee_router", AuthorityMode.RUST_SHADOW, python_fn=py)
    assert d.authority == "python"
    assert d.shadow_checked is False


# --------------------------------------------------------------------------
# rust_authority_with_python_shadow (Rust authority, Python checks)
# --------------------------------------------------------------------------

def test_rust_authority_with_shadow_agreement():
    py, ru = _Counter(PY_RESULT), _Counter(RUST_SAME)
    d = decide(
        "fee_router",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=py,
        rust_fn=ru,
    )
    assert d.authority == "rust"
    assert d.result == RUST_SAME
    assert d.shadow_checked is True
    assert d.agreed is True
    assert py.calls == 1 and ru.calls == 1


def test_rust_authority_with_shadow_disagreement_fails_closed():
    py, ru = _Counter(PY_RESULT), _Counter(RUST_DIFFERENT)
    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=py,
            rust_fn=ru,
        )


def test_rust_authority_with_shadow_rejects_none_none_default_agreement():
    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=_Counter(None),
            rust_fn=_Counter(None),
        )


def test_rust_authority_with_shadow_requires_engine():
    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=_Counter(PY_RESULT),
            rust_fn=None,
        )

    def rust_unavailable():
        raise RustUnavailable("not built")

    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=_Counter(PY_RESULT),
            rust_fn=rust_unavailable,
        )


def test_rust_authority_error_fails_closed():
    def rust_err():
        raise RuntimeError("timeout")

    with pytest.raises(AuthorityError):
        decide(
            "fee_router",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=_Counter(PY_RESULT),
            rust_fn=rust_err,
        )


# --------------------------------------------------------------------------
# rust_authority (Rust only)
# --------------------------------------------------------------------------

def test_rust_authority_runs_only_rust():
    ru = _Counter(RUST_SAME)
    d = decide("fee_router", AuthorityMode.RUST_AUTHORITY, python_fn=_boom, rust_fn=ru)
    assert d.authority == "rust"
    assert d.result == RUST_SAME
    assert d.shadow_checked is False
    assert ru.calls == 1  # python_fn (_boom) never called


def test_rust_authority_requires_engine():
    with pytest.raises(AuthorityError):
        decide("fee_router", AuthorityMode.RUST_AUTHORITY, python_fn=_Counter(PY_RESULT), rust_fn=None)


# --------------------------------------------------------------------------
# State-root unchanged across python_authority and shadow promotion
# --------------------------------------------------------------------------

def test_state_root_unchanged_across_python_and_shadow_for_agreeing_surface():
    # For a surface where Python and Rust agree (the promotion precondition),
    # the canonical result — including post_state_root — is identical whether we
    # run as python_authority or rust_authority_with_python_shadow.
    py = _Counter(PY_RESULT)
    ru = _Counter(RUST_SAME)
    d_python = decide("state_root", AuthorityMode.PYTHON_AUTHORITY, python_fn=py)
    d_shadow = decide(
        "state_root",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=_Counter(PY_RESULT),
        rust_fn=ru,
    )
    assert d_python.result["post_state_root"] == d_shadow.result["post_state_root"]
    assert d_python.result == d_shadow.result


def test_custom_compare_is_used():
    # Agreement can be customized (e.g. compare only the state-root field).
    py = _Counter({"post_state_root": "0xroot", "note": "py"})
    ru = _Counter({"post_state_root": "0xroot", "note": "ru"})
    same_root = lambda a, b: a["post_state_root"] == b["post_state_root"]
    d = decide(
        "state_root",
        AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        python_fn=py,
        rust_fn=ru,
        compare=same_root,
    )
    assert d.agreed is True  # differ in 'note' but agree on the root


def test_custom_compare_must_return_bool():
    def truthy_non_bool(_py, _ru):
        return "agree"

    with pytest.raises(AuthorityError, match="comparator must return bool"):
        decide(
            "state_root",
            AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            python_fn=_Counter(PY_RESULT),
            rust_fn=_Counter(RUST_SAME),
            compare=truthy_non_bool,
        )


def test_custom_compare_error_fails_closed_as_authority_error():
    def compare_raises(_py, _ru):
        raise ValueError("malformed comparator input")

    with pytest.raises(AuthorityError, match="comparator errored"):
        decide(
            "state_root",
            AuthorityMode.RUST_SHADOW,
            python_fn=_Counter(PY_RESULT),
            rust_fn=_Counter(RUST_SAME),
            compare=compare_raises,
        )


# --------------------------------------------------------------------------
# Deployment-profile policy loading + strict-profile validation
# --------------------------------------------------------------------------


def _complete_public_testnet_policy(
    per_surface_overrides=None,
    promoted_surfaces=None,
):
    per_surface = {
        surface: AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
        for surface in PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES
    }
    if per_surface_overrides:
        for surface, mode in per_surface_overrides.items():
            if mode is None:
                per_surface.pop(surface, None)
            else:
                per_surface[surface] = mode
    promoted = (
        frozenset(PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES)
        if promoted_surfaces is None
        else frozenset(promoted_surfaces)
    )
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface=per_surface,
        promoted_surfaces=promoted,
    )


def test_load_policy_defaults_when_absent():
    policy = load_authority_policy({"profile_id": "local-dev"})
    assert policy.default is AuthorityMode.PYTHON_AUTHORITY
    assert policy.per_surface == {}
    assert policy.promoted_surfaces == frozenset()


def test_load_policy_parses_section():
    profile = {
        "runtime_authority_policy": {
            "schema": "zenodex/runtime_authority_policy/v1",
            "default": "python_authority",
            "per_surface": {"fee_router": "rust_authority_with_python_shadow"},
            "promoted_surfaces": ["fee_router"],
        }
    }
    policy = load_authority_policy(profile)
    assert policy.mode_for("fee_router") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert policy.mode_for("balances") is AuthorityMode.PYTHON_AUTHORITY
    assert "fee_router" in policy.promoted_surfaces


def test_load_policy_rejects_bad_schema():
    with pytest.raises(ValueError):
        load_authority_policy({"runtime_authority_policy": {"schema": "wrong/schema"}})
    with pytest.raises(ValueError, match="runtime_authority_policy schema"):
        load_authority_policy({"runtime_authority_policy": {"default": "python_authority"}})


def test_load_policy_rejects_unknown_section_keys():
    with pytest.raises(ValueError, match="runtime_authority_policy has unknown keys"):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "default": "python_authority",
                    "per_surface": {},
                    "promoted_surfaces": [],
                    "promoted_surface": ["fee_router"],
                }
            }
        )


def test_load_policy_rejects_bad_mode():
    with pytest.raises(ValueError):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "per_surface": {"x": "rust_maybe"},
                }
            }
        )


def test_load_policy_rejects_non_string_surface_ids():
    with pytest.raises(TypeError, match="per_surface surface id must be a string"):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "per_surface": {123: "python_authority"},
                }
            }
        )
    with pytest.raises(TypeError, match="promoted_surfaces surface id must be a string"):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "promoted_surfaces": ["fee_router", 123],
                }
            }
        )


def test_load_policy_rejects_blank_or_duplicate_surface_ids():
    with pytest.raises(ValueError, match="surface id must be non-empty"):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "per_surface": {" fee_router": "python_authority"},
                }
            }
        )
    with pytest.raises(ValueError, match="promoted_surfaces must not contain duplicates"):
        load_authority_policy(
            {
                "runtime_authority_policy": {
                    "schema": "zenodex/runtime_authority_policy/v1",
                    "promoted_surfaces": ["fee_router", "fee_router"],
                }
            }
        )


def test_production_profile_rejects_half_configured_rust_authority():
    # fee_router promoted to rust authority but NOT in promoted_surfaces.
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"fee_router": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW},
        promoted_surfaces=frozenset(),
    )
    with pytest.raises(AuthorityError):
        validate_authority_policy(policy, profile_id="production-strict")


def test_production_profile_rejects_rust_authority_before_release_schema():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"fee_router": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW},
        promoted_surfaces=frozenset({"fee_router"}),
    )
    with pytest.raises(AuthorityError, match="explicit release profile/schema"):
        validate_authority_policy(policy, profile_id="production-strict")


def test_public_testnet_profile_requires_every_admitted_rust_surface():
    # Partial-CBC surfaces are excluded from the required Rust-authority set, so
    # use fee_router to test the missing-surface check.
    policy = _complete_public_testnet_policy(
        per_surface_overrides={"fee_router": None},
        promoted_surfaces=PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES - {"fee_router"},
    )
    with pytest.raises(AuthorityError, match="missing trusted-core authority surfaces"):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_rejects_partial_cbc_rust_repromotion():
    policy = _complete_public_testnet_policy(
        per_surface_overrides={
            "zusd": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
        },
        promoted_surfaces=PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES | {"zusd"},
    )
    with pytest.raises(AuthorityError, match="partial-CBC surfaces"):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_requires_shadow_checked_rust_authority():
    policy = _complete_public_testnet_policy(
        per_surface_overrides={"fee_router": AuthorityMode.RUST_SHADOW}
    )
    with pytest.raises(
        AuthorityError,
        match="trusted-core surfaces must use rust_authority_with_python_shadow",
    ):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_rejects_non_trusted_core_surface():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"debug_dashboard": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW},
        promoted_surfaces=frozenset({"debug_dashboard"}),
    )
    with pytest.raises(AuthorityError, match="non-trusted-core surfaces"):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_rejects_half_configured_rust_authority():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"canonical": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW},
        promoted_surfaces=frozenset(),
    )
    with pytest.raises(AuthorityError):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_rejects_stale_promoted_surface():
    policy = _complete_public_testnet_policy(
        per_surface_overrides={"fee_router": AuthorityMode.RUST_SHADOW}
    )
    with pytest.raises(
        AuthorityError,
        match="trusted-core surfaces must use rust_authority_with_python_shadow",
    ):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_public_testnet_profile_rejects_pure_rust_authority():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"fee_router": AuthorityMode.RUST_AUTHORITY},
        promoted_surfaces=frozenset({"fee_router"}),
    )
    with pytest.raises(AuthorityError, match="pure rust_authority is not admitted"):
        validate_authority_policy(policy, profile_id="public-testnet")


def test_production_profile_rejects_unknown_promoted_surface():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={},
        promoted_surfaces=frozenset({"fee_routre"}),
    )
    with pytest.raises(AuthorityError, match="non-trusted-core surfaces"):
        validate_authority_policy(policy, profile_id="production-strict")


def test_production_profile_rejects_blanket_rust_default():
    policy = AuthorityPolicy(
        default=AuthorityMode.RUST_AUTHORITY,
        per_surface={},
        promoted_surfaces=frozenset({"fee_router"}),
    )
    with pytest.raises(AuthorityError):
        validate_authority_policy(policy, profile_id="production-strict")


def test_non_strict_profile_allows_experimentation():
    policy = AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"debug_dashboard": AuthorityMode.RUST_AUTHORITY},
        promoted_surfaces=frozenset(),
    )
    # local-dev is not strict → advisory only, must not raise.
    validate_authority_policy(policy, profile_id="local-dev")


# --------------------------------------------------------------------------
# Audit metadata
# --------------------------------------------------------------------------

def test_real_deploy_profiles_load_and_validate():
    # End-to-end: every shipped config/deploy/*.yaml carries a parseable
    # runtime_authority_policy that validates for its own profile_id (the
    # "authority mode is part of deployment facts" requirement). The strict
    # production profile must be all-Python (no promoted surfaces yet).
    yaml = pytest.importorskip("yaml")
    deploy_dir = REPO / "config" / "deploy"
    seen = set()
    for path in sorted(deploy_dir.glob("*.yaml")):
        profile = yaml.safe_load(path.read_text(encoding="utf-8"))
        profile_id = profile["profile_id"]
        seen.add(profile_id)
        policy = load_authority_policy(profile)
        validate_authority_policy(policy, profile_id=profile_id)  # must not raise
        if profile_id == "public-testnet":
            assert policy.default is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("balances") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
            assert policy.mode_for("burn_receipts") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
            assert policy.mode_for("canonical") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("cpmm_settlement") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("fee_router") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
            assert policy.mode_for("perp_math") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("perp_stateful") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("state_root") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.mode_for("replay_guard") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
            assert policy.mode_for("zusd") is AuthorityMode.PYTHON_AUTHORITY
            assert policy.promoted_surfaces == frozenset(
                {
                    "balances",
                    "burn_receipts",
                    "fee_router",
                    "replay_guard",
                }
            )
        if profile_id == "production-strict":
            assert policy.default is AuthorityMode.PYTHON_AUTHORITY
            assert policy.promoted_surfaces == frozenset()
            assert all(
                m is AuthorityMode.PYTHON_AUTHORITY for m in policy.per_surface.values()
            )
    assert {"local-dev", "public-testnet", "production-strict"} <= seen


def test_decision_metadata_is_receipt_visible():
    d = AuthorityDecision(
        surface="fee_router",
        mode=AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
        authority="rust",
        result=RUST_SAME,
        shadow_checked=True,
        agreed=True,
    )
    md = d.metadata()
    assert md["surface"] == "fee_router"
    assert md["authority_mode"] == "rust_authority_with_python_shadow"
    assert md["decided_by"] == "rust"
    assert md["shadow_checked"] is True
    assert md["shadow_agreed"] is True
    assert "result" not in md  # metadata carries no payload
