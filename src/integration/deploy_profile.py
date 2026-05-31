"""Deploy-profile parsing and runtime consistency enforcement.

The `config/deploy/*.yaml` profiles declare a deployment's security policy. This
module checks active process facts against the subset of those policies that maps
directly to server-side runtime flags, then the API server can fail closed before
binding a socket.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping

import yaml

from src.runtime.authority import AuthorityError, load_authority_policy, validate_authority_policy

DEPLOY_PROFILE_SCHEMA = "zenodex/deployment_profile/v1"
_DEPLOY_DIR = Path(__file__).resolve().parents[2] / "config" / "deploy"

RUNTIME_FACT_KEYS = (
    "sensitive_api_enabled",
    "external_auth_enforced",
    "auth_bearer_token_set",
    "allow_demo_token_auth",
    "legacy_demo_token_active",
    "confidential_sealed_bid_allow_in_memory_state",
    "confidential_sealed_bid_allow_fixture_settlement",
    "confidential_sealed_bid_return_signed_tau_tx_payload",
    "perps_wallet_allow_local_signing",
    "perps_wallet_return_signed_tau_tx_payload",
    "zusd_tau_wallet_allow_local_signing",
    "zusd_tau_wallet_return_signed_tau_tx_payload",
    "zusd_monetary_wallet_allow_local_signing",
    "autotrader_live_allow_local_signing",
)


def load_deploy_profile(profile: str) -> dict[str, Any]:
    """Load a deploy profile by id (`config/deploy/<id>.yaml`) or path."""

    if not isinstance(profile, str) or not profile.strip():
        raise ValueError("profile must be a non-empty string")
    candidate = Path(profile)
    if candidate.suffix in (".yaml", ".yml") and candidate.is_file():
        path = candidate
    else:
        path = _DEPLOY_DIR / f"{profile}.yaml"
    if not path.is_file():
        raise FileNotFoundError(f"deploy profile not found: {profile!r} (looked at {path})")
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("deploy profile must be a mapping")
    if obj.get("schema") != DEPLOY_PROFILE_SCHEMA:
        raise ValueError(f"unexpected deploy profile schema: {obj.get('schema')!r}")
    return dict(obj)


def evaluate_deploy_profile_consistency(
    profile: Mapping[str, Any], runtime_facts: Mapping[str, Any]
) -> tuple[str, ...]:
    """Return conflicts between a deployment profile and active runtime facts."""

    if not isinstance(profile, Mapping):
        raise TypeError("profile must be a mapping")
    if not isinstance(runtime_facts, Mapping):
        raise TypeError("runtime_facts must be a mapping")

    raw_profile_id = profile.get("profile_id", "?")
    if isinstance(raw_profile_id, str) and raw_profile_id == raw_profile_id.strip() and raw_profile_id:
        profile_id = raw_profile_id
    else:
        profile_id = "?"
    key_policy = profile.get("key_policy") or {}
    runtime_policy = profile.get("runtime_policy") or {}
    required_auth = profile.get("required_auth") or {}

    conflicts: list[str] = []

    if profile_id == "?":
        conflicts.append("[?] profile_id must be a non-empty whitespace-trimmed string")
    if not isinstance(key_policy, Mapping):
        conflicts.append(f"[{profile_id}] key_policy must be a mapping")
        key_policy = {}
    if not isinstance(runtime_policy, Mapping):
        conflicts.append(f"[{profile_id}] runtime_policy must be a mapping")
        runtime_policy = {}
    if not isinstance(required_auth, Mapping):
        conflicts.append(f"[{profile_id}] required_auth must be a mapping")
        required_auth = {}

    def fact(name: str) -> bool:
        value = runtime_facts.get(name, False)
        if isinstance(value, bool):
            return value
        conflicts.append(
            f"[{profile_id}] runtime fact {name!r} must be a bool, got {type(value).__name__}"
        )
        return False

    if key_policy.get("raw_private_key_flags_allowed") is False:
        raw_key_flags = {
            "PERPS_WALLET_ALLOW_LOCAL_SIGNING": "perps_wallet_allow_local_signing",
            "PERPS_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD": "perps_wallet_return_signed_tau_tx_payload",
            "ZUSD_TAU_WALLET_ALLOW_LOCAL_SIGNING": "zusd_tau_wallet_allow_local_signing",
            "ZUSD_TAU_WALLET_RETURN_SIGNED_TAU_TX_PAYLOAD": "zusd_tau_wallet_return_signed_tau_tx_payload",
            "ZUSD_MONETARY_WALLET_ALLOW_LOCAL_SIGNING": "zusd_monetary_wallet_allow_local_signing",
            "AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING": "autotrader_live_allow_local_signing",
            "CONFIDENTIAL_SEALED_BID_RETURN_SIGNED_TAU_TX_PAYLOAD": (
                "confidential_sealed_bid_return_signed_tau_tx_payload"
            ),
        }
        for env_name, fact_name in raw_key_flags.items():
            if fact(fact_name):
                conflicts.append(
                    f"[{profile_id}] key_policy.raw_private_key_flags_allowed=false "
                    f"but {env_name} is enabled"
                )

    if runtime_policy.get("local_only_routes_allowed") is False:
        local_only_flags = {
            "ALLOW_DEMO_TOKEN_AUTH": "allow_demo_token_auth",
            "DEMO_API_TOKEN": "legacy_demo_token_active",
            "CONFIDENTIAL_SEALED_BID_ALLOW_IN_MEMORY_STATE": (
                "confidential_sealed_bid_allow_in_memory_state"
            ),
            "CONFIDENTIAL_SEALED_BID_ALLOW_FIXTURE_SETTLEMENT": (
                "confidential_sealed_bid_allow_fixture_settlement"
            ),
        }
        for env_name, fact_name in local_only_flags.items():
            if fact(fact_name):
                conflicts.append(
                    f"[{profile_id}] runtime_policy.local_only_routes_allowed=false "
                    f"but {env_name} is active"
                )

    public_auth = required_auth.get("public_api")
    if public_auth in ("bearer_token", "bearer_token_or_reverse_proxy"):
        has_auth_boundary = fact("auth_bearer_token_set") or fact("external_auth_enforced")
        if fact("sensitive_api_enabled") and not has_auth_boundary:
            conflicts.append(
                f"[{profile_id}] required_auth.public_api={public_auth} but sensitive APIs "
                "are enabled without a bearer token or external auth boundary"
            )
    try:
        authority_policy = load_authority_policy(profile)
        validate_authority_policy(authority_policy, profile_id=profile_id)
    except (AuthorityError, ValueError, TypeError) as exc:
        conflicts.append(f"[{profile_id}] runtime_authority_policy invalid: {exc}")
    return tuple(dict.fromkeys(conflicts))


def enforced_policy_fields() -> tuple[str, ...]:
    return (
        "key_policy.raw_private_key_flags_allowed",
        "runtime_policy.local_only_routes_allowed",
        "required_auth.public_api",
        "runtime_authority_policy",
    )
