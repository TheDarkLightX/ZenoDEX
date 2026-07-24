"""ZenoLedger v0 profile and checkpoint admission policy."""

from __future__ import annotations

from copy import deepcopy
from enum import Enum
from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    hash_v0,
    validate_checkpoint_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

PROFILE_SCHEMA_V0 = "zenodex/zeno_ledger/testnet_profile/v0"

DEPLOYMENT_MODE_LOCAL_SANDBOX_V0 = "local_sandbox"
DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0 = "zeno_sovereign_testnet"
DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0 = "tau_exclusive_release"

TOKEN_SCOPE_NONE_V0 = "none"
TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0 = "zeno_ledger_testnet"
TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0 = "tau_net_exclusive"

DEPLOYMENT_MODES_V0 = frozenset(
    {
        DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
        DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
        DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
    }
)

TOKEN_SCOPES_V0 = frozenset(
    {
        TOKEN_SCOPE_NONE_V0,
        TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
        TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0,
    }
)


class ProofRequiredAuthorityRejectReasonV0(str, Enum):
    """Stable reasons for quarantining proof-required V0 authority paths."""

    AUTHENTICATED_CRYPTOGRAPHIC_AUTHORITY_UNAVAILABLE = (
        "proof_required.authenticated_cryptographic_authority_unavailable_v0"
    )


class ProofRequiredAuthorityErrorV0(ValueError):
    """A proof-required V0 consumer reached a boundary without proof authority."""

    def __init__(
        self,
        *,
        reason: ProofRequiredAuthorityRejectReasonV0,
        boundary: str,
    ) -> None:
        self.reason = reason
        self.boundary = boundary
        super().__init__(f"{reason.value}:{boundary}")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_list(value: object, *, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not allow_empty and value == "":
        raise ValueError(f"{name} must be non-empty")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def profile_content_hash_v0(profile: Mapping[str, Any]) -> str:
    obj = dict(_require_mapping(profile, name="profile"))
    obj.pop("profile_id", None)
    return hash_v0("testnet_profile_v0", obj)


def validate_zeno_ledger_profile_v0(profile: Mapping[str, Any]) -> None:
    obj = _require_mapping(profile, name="profile")
    expected = {
        "schema",
        "profile_id",
        "profile_name",
        "deployment_mode",
        "chain_id",
        "accepted_config_digests",
        "accepted_sequencer_set_hashes",
        "proof_required",
        "body_required",
        "tau_net_adapter_required",
        "token_policy",
        "bridge_policy",
    }
    if set(obj.keys()) != expected:
        raise ValueError("profile keys mismatch")
    if obj.get("schema") != PROFILE_SCHEMA_V0:
        raise ValueError("profile schema mismatch")
    profile_id = _require_root(obj.get("profile_id"), name="profile.profile_id")
    expected_profile_id = profile_content_hash_v0(obj)
    if profile_id != expected_profile_id:
        raise ValueError("profile_id mismatch")
    _require_str(obj.get("profile_name"), name="profile.profile_name")
    chain_id = _require_str(obj.get("chain_id"), name="profile.chain_id")
    mode = _require_str(obj.get("deployment_mode"), name="profile.deployment_mode")
    if mode not in DEPLOYMENT_MODES_V0:
        raise ValueError("deployment_mode is not allowed")

    config_digests = _require_list(obj.get("accepted_config_digests"), name="accepted_config_digests")
    sequencer_hashes = _require_list(
        obj.get("accepted_sequencer_set_hashes"),
        name="accepted_sequencer_set_hashes",
    )
    if not config_digests:
        raise ValueError("accepted_config_digests must be non-empty")
    if not sequencer_hashes:
        raise ValueError("accepted_sequencer_set_hashes must be non-empty")
    for i, digest in enumerate(config_digests):
        _require_root(digest, name=f"accepted_config_digests[{i}]")
    for i, digest in enumerate(sequencer_hashes):
        _require_root(digest, name=f"accepted_sequencer_set_hashes[{i}]")

    proof_required = _require_bool(obj.get("proof_required"), name="proof_required")
    body_required = _require_bool(obj.get("body_required"), name="body_required")
    tau_net_adapter_required = _require_bool(
        obj.get("tau_net_adapter_required"),
        name="tau_net_adapter_required",
    )

    token_policy = _require_mapping(obj.get("token_policy"), name="token_policy")
    token_expected = {
        "token_symbol",
        "token_asset_id",
        "issuance_scope",
        "tau_net_exclusive",
        "external_minting_allowed",
        "non_tau_deployment_allowed",
    }
    if set(token_policy.keys()) != token_expected:
        raise ValueError("token_policy keys mismatch")
    token_symbol = _require_str(
        token_policy.get("token_symbol"),
        name="token_policy.token_symbol",
        allow_empty=True,
    )
    token_asset_id = _require_root(token_policy.get("token_asset_id"), name="token_policy.token_asset_id")
    issuance_scope = _require_str(token_policy.get("issuance_scope"), name="token_policy.issuance_scope")
    if issuance_scope not in TOKEN_SCOPES_V0:
        raise ValueError("token issuance_scope is not allowed")
    tau_net_exclusive = _require_bool(
        token_policy.get("tau_net_exclusive"),
        name="token_policy.tau_net_exclusive",
    )
    external_minting_allowed = _require_bool(
        token_policy.get("external_minting_allowed"),
        name="token_policy.external_minting_allowed",
    )
    non_tau_deployment_allowed = _require_bool(
        token_policy.get("non_tau_deployment_allowed"),
        name="token_policy.non_tau_deployment_allowed",
    )

    bridge_policy = _require_mapping(obj.get("bridge_policy"), name="bridge_policy")
    bridge_expected = {
        "bridge_value_enabled",
        "requires_tau_checkpoint",
        "requires_proof_journal",
    }
    if set(bridge_policy.keys()) != bridge_expected:
        raise ValueError("bridge_policy keys mismatch")
    bridge_value_enabled = _require_bool(
        bridge_policy.get("bridge_value_enabled"),
        name="bridge_policy.bridge_value_enabled",
    )
    requires_tau_checkpoint = _require_bool(
        bridge_policy.get("requires_tau_checkpoint"),
        name="bridge_policy.requires_tau_checkpoint",
    )
    requires_proof_journal = _require_bool(
        bridge_policy.get("requires_proof_journal"),
        name="bridge_policy.requires_proof_journal",
    )

    if mode == DEPLOYMENT_MODE_LOCAL_SANDBOX_V0:
        if chain_id == "":
            raise ValueError("local sandbox chain_id must be non-empty")
        if tau_net_adapter_required:
            raise ValueError("local sandbox must not require Tau adapter")
        if bridge_value_enabled:
            raise ValueError("local sandbox must not enable bridge value")
        if issuance_scope != TOKEN_SCOPE_NONE_V0:
            raise ValueError("local sandbox token scope must be none")
        if token_symbol != "":
            raise ValueError("local sandbox token symbol must be empty")
        if token_asset_id != ZERO_ROOT_V0:
            raise ValueError("local sandbox token_asset_id must be zero root")
        if tau_net_exclusive or external_minting_allowed or non_tau_deployment_allowed:
            raise ValueError("local sandbox token policy must not enable token deployment")

    if mode == DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0:
        if chain_id == "":
            raise ValueError("sovereign testnet chain_id must be non-empty")
        if tau_net_adapter_required:
            raise ValueError("sovereign testnet must not require Tau adapter")
        if not body_required:
            raise ValueError("sovereign testnet requires body availability")
        if bridge_value_enabled:
            raise ValueError("sovereign testnet must not enable bridge value")
        if requires_tau_checkpoint:
            raise ValueError("sovereign testnet must not require Tau checkpoint")
        if requires_proof_journal and not proof_required:
            raise ValueError("sovereign testnet bridge policy cannot require proof without profile proof")
        if issuance_scope != TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0:
            raise ValueError("sovereign testnet token scope must be zeno_ledger_testnet")
        if not token_symbol:
            raise ValueError("sovereign testnet token symbol must be non-empty")
        if token_asset_id == ZERO_ROOT_V0:
            raise ValueError("sovereign testnet token_asset_id must be non-zero")
        if tau_net_exclusive:
            raise ValueError("sovereign testnet token must not be Tau Net exclusive")
        if external_minting_allowed:
            raise ValueError("sovereign testnet forbids external minting")
        if not non_tau_deployment_allowed:
            raise ValueError("sovereign testnet must permit non-Tau deployment")

    if mode == DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0:
        if not tau_net_adapter_required:
            raise ValueError("Tau-exclusive release requires Tau adapter")
        if not body_required:
            raise ValueError("Tau-exclusive release requires body availability")
        if not proof_required:
            raise ValueError("Tau-exclusive release requires proof journal")
        if not bridge_value_enabled:
            raise ValueError("Tau-exclusive release must explicitly enable bridge value")
        if not requires_tau_checkpoint:
            raise ValueError("Tau-exclusive release requires Tau checkpoint")
        if not requires_proof_journal:
            raise ValueError("Tau-exclusive release requires proof journal bridge policy")
        if issuance_scope != TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0:
            raise ValueError("Tau-exclusive release token scope must be tau_net_exclusive")
        if not token_symbol:
            raise ValueError("Tau-exclusive release token symbol must be non-empty")
        if token_asset_id == ZERO_ROOT_V0:
            raise ValueError("Tau-exclusive release token_asset_id must be non-zero")
        if not tau_net_exclusive:
            raise ValueError("Tau-exclusive release token must be Tau Net exclusive")
        if external_minting_allowed:
            raise ValueError("Tau-exclusive release forbids external minting")
        if non_tau_deployment_allowed:
            raise ValueError("Tau-exclusive release forbids non-Tau deployment")


def zeno_ledger_profile_requires_proof_authority_v0(
    profile: Mapping[str, Any],
) -> bool:
    """Return the validated profile's proof-authority requirement."""

    validate_zeno_ledger_profile_v0(profile)
    bridge_policy = _require_mapping(profile["bridge_policy"], name="bridge_policy")
    return bool(profile["proof_required"]) or bool(bridge_policy["requires_proof_journal"])


def require_production_proof_authority_v0(
    *,
    profile: Mapping[str, Any],
    boundary: str,
) -> None:
    """Quarantine V0 authority consumers until they accept authenticated facts.

    The strict Spot range verifier has its own governed cryptographic capability
    path.  This helper protects generic V0 consumers that receive only profile,
    checkpoint, metadata, or caller-authored report data.
    """

    if not isinstance(boundary, str) or boundary == "":
        raise ValueError("boundary must be a non-empty string")
    if zeno_ledger_profile_requires_proof_authority_v0(profile):
        raise ProofRequiredAuthorityErrorV0(
            reason=(
                ProofRequiredAuthorityRejectReasonV0
                .AUTHENTICATED_CRYPTOGRAPHIC_AUTHORITY_UNAVAILABLE
            ),
            boundary=boundary,
        )


def validate_checkpoint_structural_compatibility_v0(
    *,
    checkpoint: Mapping[str, Any],
    profile: Mapping[str, Any],
) -> None:
    """Validate V0 profile/checkpoint structure without granting authority."""

    validate_zeno_ledger_profile_v0(profile)
    checkpoint_obj = _require_mapping(checkpoint, name="checkpoint")
    validate_checkpoint_v0(dict(checkpoint_obj))

    if checkpoint_obj["chain_id"] != profile["chain_id"]:
        raise ValueError("checkpoint chain_id not admitted by profile")
    if checkpoint_obj["config_digest"] not in profile["accepted_config_digests"]:
        raise ValueError("checkpoint config_digest not admitted by profile")
    if checkpoint_obj["sequencer_set_hash"] not in profile["accepted_sequencer_set_hashes"]:
        raise ValueError("checkpoint sequencer_set_hash not admitted by profile")
    if bool(profile["proof_required"]) and checkpoint_obj["proof_journal_hash"] == ZERO_ROOT_V0:
        raise ValueError("checkpoint proof_journal_hash required by profile")
    bridge_policy = _require_mapping(profile["bridge_policy"], name="bridge_policy")
    if bool(bridge_policy["requires_proof_journal"]) and checkpoint_obj["proof_journal_hash"] == ZERO_ROOT_V0:
        raise ValueError("checkpoint proof_journal_hash required by bridge policy")


def validate_checkpoint_admission_v0(
    *,
    checkpoint: Mapping[str, Any],
    profile: Mapping[str, Any],
) -> None:
    """Admit structurally valid checkpoints only when V0 needs no proof authority."""

    validate_checkpoint_structural_compatibility_v0(
        checkpoint=checkpoint,
        profile=profile,
    )
    require_production_proof_authority_v0(
        profile=profile,
        boundary="checkpoint_admission_v0",
    )


def make_zeno_ledger_profile_v0(
    *,
    profile_name: str,
    deployment_mode: str,
    chain_id: str,
    accepted_config_digests: list[str],
    accepted_sequencer_set_hashes: list[str],
    proof_required: bool,
    body_required: bool,
    tau_net_adapter_required: bool,
    token_policy: Mapping[str, Any],
    bridge_policy: Mapping[str, Any],
) -> dict[str, Any]:
    profile = {
        "schema": PROFILE_SCHEMA_V0,
        "profile_id": ZERO_ROOT_V0,
        "profile_name": profile_name,
        "deployment_mode": deployment_mode,
        "chain_id": chain_id,
        "accepted_config_digests": list(accepted_config_digests),
        "accepted_sequencer_set_hashes": list(accepted_sequencer_set_hashes),
        "proof_required": proof_required,
        "body_required": body_required,
        "tau_net_adapter_required": tau_net_adapter_required,
        "token_policy": dict(token_policy),
        "bridge_policy": dict(bridge_policy),
    }
    profile["profile_id"] = profile_content_hash_v0(profile)
    validate_zeno_ledger_profile_v0(profile)
    return profile


def sample_local_sandbox_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger local sandbox",
        deployment_mode=DEPLOYMENT_MODE_LOCAL_SANDBOX_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=False,
        body_required=True,
        tau_net_adapter_required=False,
        token_policy={
            "token_symbol": "",
            "token_asset_id": ZERO_ROOT_V0,
            "issuance_scope": TOKEN_SCOPE_NONE_V0,
            "tau_net_exclusive": False,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": False,
        },
        bridge_policy={
            "bridge_value_enabled": False,
            "requires_tau_checkpoint": False,
            "requires_proof_journal": False,
        },
    )


def sample_zeno_sovereign_testnet_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
    token_symbol: str,
    token_asset_id: str,
    proof_required: bool = False,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger sovereign testnet",
        deployment_mode=DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=proof_required,
        body_required=True,
        tau_net_adapter_required=False,
        token_policy={
            "token_symbol": token_symbol,
            "token_asset_id": token_asset_id,
            "issuance_scope": TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
            "tau_net_exclusive": False,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": True,
        },
        bridge_policy={
            "bridge_value_enabled": False,
            "requires_tau_checkpoint": False,
            "requires_proof_journal": proof_required,
        },
    )


def sample_tau_exclusive_release_profile_v0(
    *,
    chain_id: str,
    config_digest: str,
    sequencer_set_hash: str,
    token_symbol: str,
    token_asset_id: str,
) -> dict[str, Any]:
    return make_zeno_ledger_profile_v0(
        profile_name="ZenoLedger Tau-exclusive release",
        deployment_mode=DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
        chain_id=chain_id,
        accepted_config_digests=[config_digest],
        accepted_sequencer_set_hashes=[sequencer_set_hash],
        proof_required=True,
        body_required=True,
        tau_net_adapter_required=True,
        token_policy={
            "token_symbol": token_symbol,
            "token_asset_id": token_asset_id,
            "issuance_scope": TOKEN_SCOPE_TAU_NET_EXCLUSIVE_V0,
            "tau_net_exclusive": True,
            "external_minting_allowed": False,
            "non_tau_deployment_allowed": False,
        },
        bridge_policy={
            "bridge_value_enabled": True,
            "requires_tau_checkpoint": True,
            "requires_proof_journal": True,
        },
    )


def clone_profile_with_new_id_v0(profile: Mapping[str, Any], **updates: Any) -> dict[str, Any]:
    updated = deepcopy(dict(profile))
    updated.update(updates)
    updated["profile_id"] = profile_content_hash_v0(updated)
    return updated
