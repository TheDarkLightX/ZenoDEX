"""Deploy-profile parsing and runtime consistency enforcement.

The `config/deploy/*.yaml` profiles declare a deployment's security policy. This
module checks active process facts against the subset of those policies that maps
directly to server-side runtime flags, then the API server can fail closed before
binding a socket.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Mapping

import yaml

from src.runtime.authority import AuthorityError, load_authority_policy, validate_authority_policy

DEPLOY_PROFILE_SCHEMA = "zenodex/deployment_profile/v1"
_DEPLOY_DIR = Path(__file__).resolve().parents[2] / "config" / "deploy"
_DEPLOY_PROFILE_ID_PATTERN = re.compile(r"^[a-z0-9](?:[a-z0-9-]*[a-z0-9])?$")
_DEPLOY_PROFILE_IDS = frozenset(("local-dev", "production-strict", "public-testnet"))

# Allowed top-level profile keys. A profile carrying any other top-level key is
# rejected at load (fail closed): a mistyped policy block (e.g. ``runtime_polciy``)
# must not silently degrade to ``{}`` and thereby disable the corresponding
# runtime conflict check in ``evaluate_deploy_profile_consistency`` below. Adding
# a new policy block requires extending this allowlist (and bumping the schema if
# the contract changes), keeping the profile contract explicit.
ALLOWED_PROFILE_KEYS = frozenset(
    {
        "schema",
        "profile_id",
        "threat_model",
        "allowed_routes",
        "required_auth",
        "key_policy",
        "proof_policy",
        "upba_policy",
        "peer_policy",
        "gossip_policy",
        "observability_policy",
        "oracle_policy",
        "runtime_policy",
        "runtime_authority_policy",
    }
)

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
    "dex_routing_oracle_adapter_required",
    "zusd_oracle_adapter_required",
    "zusd_oracle_authorization_required",
    "zusd_monetary_wallet_oracle_authorization_required",
    "perps_clearinghouse_settle_oracle_adapter_required",
    "perps_clearinghouse_settle_oracle_authorization_required",
    "perps_isolated_settle_oracle_adapter_required",
    "perps_isolated_partial_liquidate_oracle_adapter_required",
    "perps_isolated_settle_oracle_authorization_required",
    "enabled_routes",
)

_KNOWN_ALLOWED_ROUTES = frozenset({"health", "local_demo", "signed_intents", "public_bundle", "peer_check"})


def _validate_deploy_profile_id(profile: str) -> str:
    """Return a safe deploy profile id.

    Contract:
    - Precondition: ``profile`` is a non-empty string supplied at the process boundary.
    - Invariant: profile ids are opaque ids, never filesystem paths.
    - Postcondition: the returned id maps only to ``config/deploy/<id>.yaml``.
    """

    if not isinstance(profile, str):
        raise ValueError("profile must be a non-empty string")
    profile_id = profile.strip()
    if not profile_id:
        raise ValueError("profile must be a non-empty string")
    if not _DEPLOY_PROFILE_ID_PATTERN.fullmatch(profile_id):
        raise ValueError(f"invalid deploy profile id: {profile!r}")
    if profile_id not in _DEPLOY_PROFILE_IDS:
        raise ValueError(f"unknown deploy profile id: {profile_id!r}")
    return profile_id


def _deploy_profile_path(profile_id: str) -> Path:
    """Resolve a validated profile id to the immutable deploy-profile directory."""

    path = (_DEPLOY_DIR / f"{profile_id}.yaml").resolve(strict=False)
    deploy_dir = _DEPLOY_DIR.resolve(strict=True)
    if path.parent != deploy_dir:
        raise ValueError(f"invalid deploy profile path for id: {profile_id!r}")
    return path


def load_deploy_profile(profile: str) -> dict[str, Any]:
    """Load a deploy profile by id from ``config/deploy/<id>.yaml`` only.

    Profile ids are opaque allowlisted identifiers, never filesystem paths.
    Arbitrary ``.yaml``/``.yml`` path inputs are rejected.
    """

    profile_id = _validate_deploy_profile_id(profile)
    path = _deploy_profile_path(profile_id)
    if not path.is_file():
        raise FileNotFoundError(f"deploy profile not found: {profile_id!r} (looked at {path})")
    obj = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError("deploy profile must be a mapping")
    unknown_keys = sorted(set(obj.keys()) - ALLOWED_PROFILE_KEYS)
    if unknown_keys:
        raise ValueError(f"deploy profile has unknown top-level keys: {unknown_keys}")
    if obj.get("schema") != DEPLOY_PROFILE_SCHEMA:
        raise ValueError(f"unexpected deploy profile schema: {obj.get('schema')!r}")
    file_profile_id = obj.get("profile_id")
    if not isinstance(file_profile_id, str) or file_profile_id != file_profile_id.strip() or not file_profile_id:
        raise ValueError("deploy profile_id must be a non-empty whitespace-trimmed string")
    if file_profile_id != profile_id:
        raise ValueError(
            f"deploy profile id mismatch: requested {profile_id!r}, file declares {file_profile_id!r}"
        )
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
    oracle_policy = profile.get("oracle_policy") or {}
    allowed_routes_raw = profile.get("allowed_routes") or ()

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
    if not isinstance(oracle_policy, Mapping):
        conflicts.append(f"[{profile_id}] oracle_policy must be a mapping")
        oracle_policy = {}
    if (
        not isinstance(allowed_routes_raw, list)
        or not allowed_routes_raw
        or not all(isinstance(route, str) and route for route in allowed_routes_raw)
    ):
        conflicts.append(f"[{profile_id}] allowed_routes must be a non-empty string list")
        allowed_routes: frozenset[str] = frozenset()
    else:
        allowed_routes = frozenset(allowed_routes_raw)
        unknown_allowed = sorted(allowed_routes - _KNOWN_ALLOWED_ROUTES)
        if unknown_allowed:
            conflicts.append(f"[{profile_id}] allowed_routes contains unknown routes: {unknown_allowed}")

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

    oracle_runtime_flags = {
        "dex_routing_oracle_adapter_required": (
            "DEX_ROUTING_ORACLE_ADAPTER_REQUIRED",
            "dex_routing_oracle_adapter_required",
        ),
        "zusd_oracle_adapter_required": (
            "ZUSD_ORACLE_ADAPTER_REQUIRED",
            "zusd_oracle_adapter_required",
        ),
        "zusd_oracle_authorization_required": (
            "ZUSD_ORACLE_AUTHORIZATION_REQUIRED",
            "zusd_oracle_authorization_required",
        ),
        "zusd_monetary_wallet_oracle_authorization_required": (
            "ZUSD_MONETARY_WALLET_ORACLE_AUTHORIZATION_REQUIRED",
            "zusd_monetary_wallet_oracle_authorization_required",
        ),
        "perps_clearinghouse_settle_oracle_adapter_required": (
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            "perps_clearinghouse_settle_oracle_adapter_required",
        ),
        "perps_clearinghouse_settle_oracle_authorization_required": (
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            "perps_clearinghouse_settle_oracle_authorization_required",
        ),
        "perps_isolated_settle_oracle_adapter_required": (
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH",
            "perps_isolated_settle_oracle_adapter_required",
        ),
        "perps_isolated_partial_liquidate_oracle_adapter_required": (
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            "perps_isolated_partial_liquidate_oracle_adapter_required",
        ),
        "perps_isolated_settle_oracle_authorization_required": (
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE_EPOCH",
            "perps_isolated_settle_oracle_authorization_required",
        ),
    }
    for policy_key, (env_name, fact_name) in oracle_runtime_flags.items():
        required = oracle_policy.get(policy_key)
        if required is None:
            continue
        if not isinstance(required, bool):
            conflicts.append(f"[{profile_id}] oracle_policy.{policy_key} must be bool")
            continue
        if required and not fact(fact_name):
            conflicts.append(
                f"[{profile_id}] oracle_policy.{policy_key}=true but {env_name} is not enabled"
            )

    public_auth = required_auth.get("public_api")
    if public_auth in ("bearer_token", "bearer_token_or_reverse_proxy"):
        has_auth_boundary = fact("auth_bearer_token_set") or fact("external_auth_enforced")
        if fact("sensitive_api_enabled") and not has_auth_boundary:
            conflicts.append(
                f"[{profile_id}] required_auth.public_api={public_auth} but sensitive APIs "
                "are enabled without a bearer token or external auth boundary"
            )
    enabled_routes_raw = runtime_facts.get("enabled_routes", ())
    if enabled_routes_raw:
        if (
            not isinstance(enabled_routes_raw, (tuple, list, set, frozenset))
            or not all(isinstance(route, str) and route for route in enabled_routes_raw)
        ):
            conflicts.append(f"[{profile_id}] runtime fact 'enabled_routes' must be a string collection")
        else:
            for route in sorted(frozenset(enabled_routes_raw) - allowed_routes):
                conflicts.append(f"[{profile_id}] allowed_routes does not permit enabled route {route!r}")
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
        "allowed_routes",
        "required_auth.public_api",
        "oracle_policy",
        "runtime_authority_policy",
    )
