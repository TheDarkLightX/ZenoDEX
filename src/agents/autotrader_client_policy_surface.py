from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Mapping

from .policy_artifacts import StrategyPolicyArtifact, StrategySourceArtifact, TauPolicyBundle
from .strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyControls,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)

AUTOTRADER_CLIENT_POLICY_SURFACE_SCHEMA = "zenodex/autotrader-client-policy-surface/v1"
_USER_RULE_SOURCE_FORM = "autotrader_user_rule_bundle"


def _canonical_json_bytes(payload: object) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_hex(payload: object) -> str:
    return "0x" + hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


@dataclass(frozen=True)
class AutoTraderClientPolicySurface:
    strategy: StrategyIR
    source_form: str | None = "compiled_strategy_ir"
    source_preset_id: str | None = None
    source_artifact_hash: str | None = None
    tau_policy_bundle_hash: str | None = None
    policy_artifact_hash: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.strategy, StrategyIR):
            raise TypeError("strategy must be a StrategyIR")
        for name in (
            "source_form",
            "source_preset_id",
            "source_artifact_hash",
            "tau_policy_bundle_hash",
            "policy_artifact_hash",
        ):
            value = getattr(self, name)
            if value is not None and (not isinstance(value, str) or not value.strip()):
                raise ValueError(f"{name} must be a non-empty string when present")
        if self.source_preset_id is not None and self.source_form != _USER_RULE_SOURCE_FORM:
            raise ValueError("source_preset_id requires autotrader_user_rule_bundle source_form")

    def to_unsigned_dict(self) -> dict[str, Any]:
        strategy = self.strategy
        return {
            "schema": AUTOTRADER_CLIENT_POLICY_SURFACE_SCHEMA,
            "strategy_id": strategy.strategy_id,
            "strategy_hash": strategy.strategy_hash_hex(),
            "owner_pubkey": strategy.owner_pubkey,
            "policy_backend": strategy.policy_backend.value,
            "strategy_logic": {
                "template": strategy.template.value,
                "asset_universe": list(strategy.asset_universe),
                "allowed_actions": [action.value for action in strategy.allowed_actions],
                "template_params": dict(strategy.template_params),
            },
            "hard_local_guards": {
                "notional_caps": strategy.notional_caps.to_dict(),
                "risk_limits": strategy.risk_limits.to_dict(),
                "strategy_window": strategy.strategy_window.to_dict(),
                "controls": strategy.controls.to_dict(),
            },
            "assurance_artifacts": {
                "tau_policy_specs": list(strategy.tau_policy_specs),
                "source_form": self.source_form,
                "source_preset_id": self.source_preset_id,
                "source_artifact_hash": self.source_artifact_hash,
                "tau_policy_bundle_hash": self.tau_policy_bundle_hash,
                "policy_artifact_hash": self.policy_artifact_hash,
            },
            "posture": {
                "client_side_default": True,
                "quote_receipts_required": bool(strategy.risk_limits.require_quote_receipts),
                "kill_switch_enabled": bool(strategy.controls.kill_switch_enabled),
                "tau_backend_selected": strategy.policy_backend is PolicyBackend.TAU,
                "tau_specs_bound": len(strategy.tau_policy_specs) > 0,
                "assurance_bundle_present": self.tau_policy_bundle_hash is not None,
                "signed_policy_present": self.policy_artifact_hash is not None,
            },
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["client_policy_surface_hash"] = self.client_policy_surface_hash_hex()
        return payload

    def client_policy_surface_hash_hex(self) -> str:
        return _sha256_hex(self.to_unsigned_dict())


def build_autotrader_client_policy_surface(
    *,
    strategy: StrategyIR,
    source_artifact: StrategySourceArtifact | None = None,
    source_preset_id: str | None = None,
    tau_policy_bundle: TauPolicyBundle | None = None,
    policy_artifact: StrategyPolicyArtifact | None = None,
) -> AutoTraderClientPolicySurface:
    if not isinstance(strategy, StrategyIR):
        raise TypeError("strategy must be a StrategyIR")
    strategy_hash = strategy.strategy_hash_hex()
    owner_pubkey = strategy.owner_pubkey

    source_form: str | None = "compiled_strategy_ir"
    source_artifact_hash: str | None = None
    if source_artifact is not None:
        if not isinstance(source_artifact, StrategySourceArtifact):
            raise TypeError("source_artifact must be a StrategySourceArtifact")
        if source_artifact.strategy.strategy_hash_hex() != strategy_hash:
            raise ValueError("source artifact strategy hash mismatch")
        source_form = source_artifact.source_form
        source_artifact_hash = source_artifact.source_artifact_hash_hex()
    if source_preset_id is not None:
        if not isinstance(source_preset_id, str) or not source_preset_id.strip():
            raise ValueError("source_preset_id must be a non-empty string when present")
        if source_form != _USER_RULE_SOURCE_FORM:
            raise ValueError("source_preset_id requires autotrader_user_rule_bundle source artifact")

    tau_policy_bundle_hash: str | None = None
    if tau_policy_bundle is not None:
        if not isinstance(tau_policy_bundle, TauPolicyBundle):
            raise TypeError("tau_policy_bundle must be a TauPolicyBundle")
        if tau_policy_bundle.strategy_hash != strategy_hash:
            raise ValueError("tau policy bundle strategy hash mismatch")
        if tau_policy_bundle.owner_pubkey != owner_pubkey:
            raise ValueError("tau policy bundle owner pubkey mismatch")
        if source_artifact_hash is not None and tau_policy_bundle.source_artifact_hash != source_artifact_hash:
            raise ValueError("tau policy bundle source artifact hash mismatch")
        tau_policy_bundle_hash = tau_policy_bundle.tau_policy_bundle_hash_hex()

    policy_artifact_hash: str | None = None
    if policy_artifact is not None:
        if not isinstance(policy_artifact, StrategyPolicyArtifact):
            raise TypeError("policy_artifact must be a StrategyPolicyArtifact")
        if policy_artifact.strategy.strategy_hash_hex() != strategy_hash:
            raise ValueError("policy artifact strategy hash mismatch")
        if policy_artifact.strategy.owner_pubkey != owner_pubkey:
            raise ValueError("policy artifact owner pubkey mismatch")
        if source_artifact_hash is not None and policy_artifact.source_artifact_hash != source_artifact_hash:
            raise ValueError("policy artifact source artifact hash mismatch")
        if tau_policy_bundle_hash is not None and policy_artifact.tau_policy_bundle_hash != tau_policy_bundle_hash:
            raise ValueError("policy artifact tau policy bundle hash mismatch")
        policy_artifact_hash = policy_artifact.policy_artifact_hash_hex()

    return AutoTraderClientPolicySurface(
        strategy=strategy,
        source_form=source_form,
        source_preset_id=source_preset_id,
        source_artifact_hash=source_artifact_hash,
        tau_policy_bundle_hash=tau_policy_bundle_hash,
        policy_artifact_hash=policy_artifact_hash,
    )


def autotrader_client_policy_surface_from_dict(payload: Mapping[str, Any]) -> AutoTraderClientPolicySurface:
    if not isinstance(payload, Mapping):
        raise TypeError("client policy surface payload must be an object")
    if payload.get("schema") != AUTOTRADER_CLIENT_POLICY_SURFACE_SCHEMA:
        raise ValueError("client policy surface schema mismatch")

    strategy_logic = payload.get("strategy_logic")
    hard_local_guards = payload.get("hard_local_guards")
    assurance_artifacts = payload.get("assurance_artifacts")
    if not isinstance(strategy_logic, Mapping):
        raise ValueError("client policy surface strategy_logic must be an object")
    if not isinstance(hard_local_guards, Mapping):
        raise ValueError("client policy surface hard_local_guards must be an object")
    if not isinstance(assurance_artifacts, Mapping):
        raise ValueError("client policy surface assurance_artifacts must be an object")

    strategy = StrategyIR(
        strategy_id=payload.get("strategy_id", ""),
        owner_pubkey=payload.get("owner_pubkey", ""),
        policy_backend=PolicyBackend(payload.get("policy_backend", "local")),
        template=StrategyTemplate(strategy_logic.get("template", "")),
        asset_universe=tuple(strategy_logic.get("asset_universe", ())),
        allowed_actions=tuple(StrategyAction(value) for value in strategy_logic.get("allowed_actions", ())),
        notional_caps=NotionalCaps(**dict(hard_local_guards.get("notional_caps", {}))),
        risk_limits=RiskLimits(**dict(hard_local_guards.get("risk_limits", {}))),
        strategy_window=StrategyWindow(**dict(hard_local_guards.get("strategy_window", {}))),
        controls=StrategyControls(**dict(hard_local_guards.get("controls", {}))),
        template_params=dict(strategy_logic.get("template_params", {})),
        tau_policy_specs=tuple(assurance_artifacts.get("tau_policy_specs", ())),
    )
    return AutoTraderClientPolicySurface(
        strategy=strategy,
        source_form=assurance_artifacts.get("source_form"),
        source_preset_id=assurance_artifacts.get("source_preset_id"),
        source_artifact_hash=assurance_artifacts.get("source_artifact_hash"),
        tau_policy_bundle_hash=assurance_artifacts.get("tau_policy_bundle_hash"),
        policy_artifact_hash=assurance_artifacts.get("policy_artifact_hash"),
    )
