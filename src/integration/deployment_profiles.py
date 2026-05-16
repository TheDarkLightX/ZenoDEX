"""Named DEX engine deployment profiles.

The profiles in this module are bootstrap guardrails. They do not change the
hot settlement path. They create and validate the DEX engine configurations
that a local rehearsal, public-testnet node, or production-strict deployment is
expected to run.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Literal

from ..core.dex import DexConfig
from .dex_engine import DexEngineConfig, production_config_violations
from .upba_production_config import make_upba_v1_bounded_price_grid_engine_config

DEPLOYMENT_PROFILE_LOCAL = "local"
DEPLOYMENT_PROFILE_PUBLIC_TESTNET = "public-testnet"
DEPLOYMENT_PROFILE_PRODUCTION_STRICT = "production-strict"

DeploymentProfileId = Literal["local", "public-testnet", "production-strict"]


@dataclass(frozen=True)
class DeploymentProfile:
    profile_id: DeploymentProfileId
    chain_id: str
    require_production_lint: bool
    require_strict_upba: bool
    require_intent_signature_only: bool
    require_oracle_authorization: bool


DEPLOYMENT_PROFILES: dict[str, DeploymentProfile] = {
    DEPLOYMENT_PROFILE_LOCAL: DeploymentProfile(
        profile_id=DEPLOYMENT_PROFILE_LOCAL,
        chain_id="zenodex-local",
        require_production_lint=False,
        require_strict_upba=False,
        require_intent_signature_only=False,
        require_oracle_authorization=False,
    ),
    DEPLOYMENT_PROFILE_PUBLIC_TESTNET: DeploymentProfile(
        profile_id=DEPLOYMENT_PROFILE_PUBLIC_TESTNET,
        chain_id="zenodex-public-testnet",
        require_production_lint=True,
        require_strict_upba=False,
        require_intent_signature_only=True,
        require_oracle_authorization=False,
    ),
    DEPLOYMENT_PROFILE_PRODUCTION_STRICT: DeploymentProfile(
        profile_id=DEPLOYMENT_PROFILE_PRODUCTION_STRICT,
        chain_id="zenodex-production-strict",
        require_production_lint=True,
        require_strict_upba=True,
        require_intent_signature_only=True,
        require_oracle_authorization=True,
    ),
}


def deployment_profile_ids() -> tuple[str, ...]:
    return tuple(DEPLOYMENT_PROFILES.keys())


def _profile(profile_id: str) -> DeploymentProfile:
    try:
        return DEPLOYMENT_PROFILES[str(profile_id)]
    except KeyError as exc:
        allowed = ", ".join(deployment_profile_ids())
        raise ValueError(f"unknown deployment profile: {profile_id!r}; expected one of: {allowed}") from exc


def _safe_core_config(base: DexConfig) -> DexConfig:
    return replace(
        base,
        require_all_nonces=True,
        allow_legacy_nonce_free_steps=False,
        settlement_validation="strong_proof_carrying",
        allow_snapshot_bound_quote_bindings=False,
    )


def make_dex_engine_config_for_deployment_profile(
    profile_id: DeploymentProfileId,
    *,
    base: DexEngineConfig | None = None,
) -> DexEngineConfig:
    """Return the canonical DEX engine config for a named deployment profile."""

    profile = _profile(profile_id)
    cfg = base or DexEngineConfig()
    cfg = replace(
        cfg,
        chain_id=profile.chain_id,
        allow_missing_settlement=False,
        require_settlement_match=True,
        require_intent_signatures=True,
        allow_unsigned_intents_if_tx_sender_matches=not profile.require_intent_signature_only,
        allow_external_tools=False,
        consensus_mode=True,
        enable_test_fault_injection=False,
        fault_injection=None,
        dex_config=_safe_core_config(cfg.dex_config),
    )
    if profile.require_oracle_authorization:
        cfg = replace(
            cfg,
            require_oracle_authorization_for_protected_swaps=True,
            require_oracle_authorization_for_critical_settlements=True,
        )
    if profile.require_strict_upba:
        cfg = make_upba_v1_bounded_price_grid_engine_config(cfg)
    return cfg


def deployment_profile_violations(
    profile_id: DeploymentProfileId,
    config: DexEngineConfig,
) -> tuple[str, ...]:
    """Return profile-specific reasons a config must not be admitted."""

    profile = _profile(profile_id)
    reasons: list[str] = []
    if not isinstance(config.chain_id, str) or not config.chain_id:
        reasons.append("chain_id must be non-empty")
    elif config.chain_id != profile.chain_id:
        reasons.append(f"chain_id must be {profile.chain_id!r} for {profile.profile_id}")

    if bool(config.enable_test_fault_injection) or config.fault_injection is not None:
        reasons.append("test fault injection must be disabled")

    if profile.require_production_lint:
        reasons.extend(
            production_config_violations(
                config,
                require_strict_upba=profile.require_strict_upba,
            )
        )

    if profile.require_intent_signature_only and bool(config.allow_unsigned_intents_if_tx_sender_matches):
        reasons.append("allow_unsigned_intents_if_tx_sender_matches must be false")

    if profile.require_oracle_authorization:
        if not bool(config.require_oracle_authorization_for_protected_swaps):
            reasons.append("protected swaps require oracle authorization")
        if not bool(config.require_oracle_authorization_for_critical_settlements):
            reasons.append("critical settlements require oracle authorization")

    return tuple(dict.fromkeys(reasons))


def validate_deployment_profile(
    profile_id: DeploymentProfileId,
    config: DexEngineConfig,
) -> tuple[bool, str | None]:
    reasons = deployment_profile_violations(profile_id, config)
    if reasons:
        return False, "; ".join(reasons)
    return True, None
