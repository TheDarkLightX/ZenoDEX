"""Production wallet-authority preflight for the mounted perps stream-8 lane.

This checks public key-manager, signer-registry, wallet UX, and proof posture
metadata. It does not custody keys, verify a hardware wallet, or prove perps
execution in a zkVM.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_key_manager import KEY_MANAGER_SCHEMA_V0, KEY_STATUS_ACTIVE, KeyRef
from src.integration.zeno_ledger_signer_registry import validate_signer_registry_v0
from src.integration.zeno_ledger_v0 import hash_v0


PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1 = "zenodex/perps-wallet-authority-profile/v1"
PERPS_WALLET_AUTHORITY_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-authority-status/v1"
PERPS_WALLET_AUTHORITY_PAYLOAD_KIND = "perps_wallet_authority_profile"

_REQUIRED_WALLET_UX_FLAGS = (
    "external_signer_required",
    "key_manager_required",
    "device_approval_required",
    "replay_protection_required",
)
_REQUIRED_PROOF_FLAGS = (
    "stream8_proof_intent_required",
    "state_delta_witness_required",
    "zk_or_proof_required",
)
_NOT_CLAIMED = (
    "does_not_claim_hardware_wallet_custody",
    "does_not_claim_perps_zk_execution",
    "does_not_claim_production_finality",
    "does_not_claim_oracle_truth",
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _body(profile: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(profile).items() if key != "wallet_authority_hash"}


def perps_wallet_authority_profile_hash_v1(profile: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_authority_profile_v1", _body(profile))


def build_perps_wallet_authority_profile_v1(
    *,
    authority_id: str,
    chain_id: str,
    stage: str,
    enabled: bool,
    key_manager: Mapping[str, Any],
    signer_registry: Mapping[str, Any],
    wallet_ux: Mapping[str, Any],
    proof_profile: Mapping[str, Any],
    transaction_scope: Mapping[str, Any],
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "stage": _require_nonempty_str(stage, name="stage"),
        "enabled": bool(enabled),
        "key_manager": dict(_require_mapping(key_manager, name="key_manager")),
        "signer_registry": dict(_require_mapping(signer_registry, name="signer_registry")),
        "wallet_ux": dict(_require_mapping(wallet_ux, name="wallet_ux")),
        "proof_profile": dict(_require_mapping(proof_profile, name="proof_profile")),
        "transaction_scope": dict(_require_mapping(transaction_scope, name="transaction_scope")),
    }
    return {**body, "wallet_authority_hash": perps_wallet_authority_profile_hash_v1(body)}


def _validate_key_manager_public(key_manager: Mapping[str, Any], gaps: list[str]) -> dict[str, KeyRef]:
    if key_manager.get("schema") != KEY_MANAGER_SCHEMA_V0:
        gaps.append("key manager schema mismatch")
        return {}

    key_refs_raw = key_manager.get("key_refs")
    recovery_policies_raw = key_manager.get("recovery_policies")
    if not isinstance(key_refs_raw, list):
        gaps.append("key manager key_refs must be a list")
        return {}
    if not isinstance(recovery_policies_raw, list):
        gaps.append("key manager recovery_policies must be a list")
        return {}

    body = {
        "schema": key_manager.get("schema"),
        "key_refs": key_refs_raw,
        "recovery_policies": recovery_policies_raw,
    }
    expected_hash = hash_v0("zeno_key_manager_v0", body)
    if key_manager.get("manager_hash") != expected_hash:
        gaps.append("key manager hash mismatch")

    refs: dict[str, KeyRef] = {}
    for index, raw_ref in enumerate(key_refs_raw):
        try:
            ref = KeyRef.from_public_dict(_require_mapping(raw_ref, name=f"key_refs[{index}]"))
        except Exception as exc:
            gaps.append(f"key manager key_ref {index} invalid: {exc}")
            continue
        if ref.key_id in refs:
            gaps.append(f"duplicate key manager key_id: {ref.key_id}")
            continue
        refs[ref.key_id] = ref
    if not refs:
        gaps.append("key manager has no public key refs")
    return refs


def _active_signer_entries(signer_registry: Mapping[str, Any], gaps: list[str]) -> tuple[list[Mapping[str, Any]], int]:
    try:
        validate_signer_registry_v0(signer_registry)
    except Exception as exc:
        gaps.append(f"signer registry invalid: {exc}")
        return [], 0

    if signer_registry.get("payload_kind") != PERPS_WALLET_AUTHORITY_PAYLOAD_KIND:
        gaps.append("signer registry payload_kind is not perps_wallet_authority_profile")

    threshold_obj = signer_registry.get("threshold")
    threshold = int(threshold_obj) if isinstance(threshold_obj, int) and not isinstance(threshold_obj, bool) else 0
    if threshold < 1:
        gaps.append("active signer threshold must be at least 1")

    raw_entries = signer_registry.get("signers")
    if not isinstance(raw_entries, list):
        gaps.append("signer registry signers must be a list")
        return [], threshold
    active = [
        entry
        for entry in raw_entries
        if isinstance(entry, Mapping) and entry.get("status") == KEY_STATUS_ACTIVE
    ]
    if not active:
        gaps.append("at least one active wallet signer is required")
    return active, threshold


def _validate_signer_key_bindings(
    *,
    active_signers: list[Mapping[str, Any]],
    key_refs: Mapping[str, KeyRef],
    gaps: list[str],
) -> None:
    for signer in active_signers:
        key_id = signer.get("key_id")
        if not isinstance(key_id, str) or key_id == "":
            gaps.append("active signer has missing key_id")
            continue
        ref = key_refs.get(key_id)
        if ref is None:
            gaps.append(f"active signer key_id {key_id} missing from key manager")
            continue
        if ref.status != KEY_STATUS_ACTIVE:
            gaps.append(f"active signer key_id {key_id} is not active in key manager")
        if signer.get("public_key") != ref.public_key:
            gaps.append(f"active signer key_id {key_id} public key mismatch")


def _validate_flag_profile(
    *,
    profile: Mapping[str, Any],
    required_flags: tuple[str, ...],
    profile_name: str,
    gaps: list[str],
) -> None:
    for flag in required_flags:
        if profile.get(flag) is not True:
            gaps.append(f"{profile_name}.{flag} must be true")


def _public_flag_profile(profile: Mapping[str, Any], flags: tuple[str, ...]) -> dict[str, bool]:
    return {flag: profile.get(flag) is True for flag in flags}


def _key_ref_summaries(key_refs: Mapping[str, KeyRef]) -> list[dict[str, Any]]:
    return [
        {
            "key_id": ref.key_id,
            "status": ref.status,
            "origin": ref.origin,
            "algorithm": ref.algorithm,
            "public_key": ref.public_key,
            "key_ref_hash": ref.public_dict()["key_ref_hash"],
            "recovery_policy_id": ref.recovery_policy_id,
        }
        for ref in sorted(key_refs.values(), key=lambda item: item.key_id)
    ]


def _active_signer_summaries(active_signers: list[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "signer_id": str(signer.get("signer_id", "")),
            "key_id": str(signer.get("key_id", "")),
            "weight": int(signer.get("weight", 0)) if isinstance(signer.get("weight"), int) else 0,
            "signer_hash": signer.get("signer_hash"),
        }
        for signer in sorted(active_signers, key=lambda item: (str(item.get("signer_id")), str(item.get("key_id"))))
    ]


def _transaction_scope_summary(scope: Mapping[str, Any], gaps: list[str]) -> dict[str, Any]:
    stream_key = scope.get("stream_key")
    if stream_key != "8":
        gaps.append("transaction_scope.stream_key must be 8")
    allowed_actions = scope.get("allowed_actions")
    if (
        not isinstance(allowed_actions, list)
        or len(allowed_actions) == 0
        or not all(isinstance(item, str) and item for item in allowed_actions)
    ):
        gaps.append("transaction_scope.allowed_actions must be a non-empty string list")
        allowed_actions_summary: list[str] = []
    else:
        allowed_actions_summary = sorted(set(allowed_actions))
    return {
        "stream_key": stream_key,
        "allowed_actions": allowed_actions_summary,
    }


def evaluate_perps_wallet_authority_profile_v1(
    profile: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    gaps: list[str] = []
    if profile is None:
        gaps.append("perps wallet authority profile is missing")
        return _status(
            ok=False,
            production_wallet_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            key_refs=[],
            active_signers=[],
            wallet_ux={},
            proof_profile={},
            transaction_scope={},
        )

    try:
        obj = _require_mapping(profile, name="profile")
    except Exception as exc:
        gaps.append(f"perps wallet authority profile invalid: {exc}")
        return _status(
            ok=False,
            production_wallet_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            key_refs=[],
            active_signers=[],
            wallet_ux={},
            proof_profile={},
            transaction_scope={},
        )

    if obj.get("schema") != PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1:
        gaps.append("perps wallet authority profile schema mismatch")
    if obj.get("enabled") is not True:
        gaps.append("perps wallet authority profile is not enabled")
    if obj.get("stage") != "production":
        gaps.append("perps wallet authority profile stage must be production")

    try:
        _require_nonempty_str(obj.get("authority_id"), name="authority_id")
    except Exception as exc:
        gaps.append(str(exc))
    try:
        chain_id = _require_nonempty_str(obj.get("chain_id"), name="chain_id")
        if expected_chain_id is not None and chain_id != expected_chain_id:
            gaps.append("perps wallet authority profile chain_id mismatch")
    except Exception as exc:
        gaps.append(str(exc))

    expected_hash = perps_wallet_authority_profile_hash_v1(obj)
    if obj.get("wallet_authority_hash") != expected_hash:
        gaps.append("perps wallet authority profile hash mismatch")

    key_refs: dict[str, KeyRef] = {}
    try:
        key_manager = _require_mapping(obj.get("key_manager"), name="key_manager")
        key_refs = _validate_key_manager_public(key_manager, gaps)
    except Exception as exc:
        gaps.append(f"key manager invalid: {exc}")

    active_signers: list[Mapping[str, Any]] = []
    threshold = 0
    try:
        signer_registry = _require_mapping(obj.get("signer_registry"), name="signer_registry")
        active_signers, threshold = _active_signer_entries(signer_registry, gaps)
        _validate_signer_key_bindings(active_signers=active_signers, key_refs=key_refs, gaps=gaps)
    except Exception as exc:
        gaps.append(f"signer registry invalid: {exc}")

    wallet_ux_summary: dict[str, bool] = {}
    try:
        wallet_ux = _require_mapping(obj.get("wallet_ux"), name="wallet_ux")
        wallet_ux_summary = _public_flag_profile(wallet_ux, _REQUIRED_WALLET_UX_FLAGS)
        _validate_flag_profile(
            profile=wallet_ux,
            required_flags=_REQUIRED_WALLET_UX_FLAGS,
            profile_name="wallet_ux",
            gaps=gaps,
        )
    except Exception as exc:
        gaps.append(f"wallet_ux invalid: {exc}")

    proof_profile_summary: dict[str, Any] = {}
    try:
        proof_profile = _require_mapping(obj.get("proof_profile"), name="proof_profile")
        proof_profile_summary = {
            **_public_flag_profile(proof_profile, _REQUIRED_PROOF_FLAGS),
            "runtime_proof_profile": proof_profile.get("runtime_proof_profile"),
        }
        _validate_flag_profile(
            profile=proof_profile,
            required_flags=_REQUIRED_PROOF_FLAGS,
            profile_name="proof_profile",
            gaps=gaps,
        )
        if not isinstance(proof_profile.get("runtime_proof_profile"), str) or not proof_profile.get("runtime_proof_profile"):
            gaps.append("proof_profile.runtime_proof_profile must be a non-empty string")
    except Exception as exc:
        gaps.append(f"proof_profile invalid: {exc}")

    transaction_scope_summary: dict[str, Any] = {}
    try:
        transaction_scope = _require_mapping(obj.get("transaction_scope"), name="transaction_scope")
        transaction_scope_summary = _transaction_scope_summary(transaction_scope, gaps)
    except Exception as exc:
        gaps.append(f"transaction_scope invalid: {exc}")

    production_wallet_authority = not gaps
    return _status(
        ok=production_wallet_authority,
        production_wallet_authority=production_wallet_authority,
        readiness_gaps=gaps,
        profile=obj,
        active_signer_count=len(active_signers),
        threshold=threshold,
        key_ref_count=len(key_refs),
        expected_wallet_authority_hash=expected_hash,
        key_refs=_key_ref_summaries(key_refs),
        active_signers=_active_signer_summaries(active_signers),
        wallet_ux=wallet_ux_summary,
        proof_profile=proof_profile_summary,
        transaction_scope=transaction_scope_summary,
    )


def _status(
    *,
    ok: bool,
    production_wallet_authority: bool,
    readiness_gaps: list[str],
    profile: Mapping[str, Any] | None,
    active_signer_count: int,
    threshold: int,
    key_ref_count: int,
    expected_wallet_authority_hash: str | None = None,
    key_refs: list[dict[str, Any]] | None = None,
    active_signers: list[dict[str, Any]] | None = None,
    wallet_ux: Mapping[str, Any] | None = None,
    proof_profile: Mapping[str, Any] | None = None,
    transaction_scope: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema": PERPS_WALLET_AUTHORITY_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "production_wallet_authority": bool(production_wallet_authority),
        "status": "ready" if production_wallet_authority else "blocked",
        "readiness_gaps": list(readiness_gaps),
        "authority_id": None if profile is None else profile.get("authority_id"),
        "chain_id": None if profile is None else profile.get("chain_id"),
        "stage": None if profile is None else profile.get("stage"),
        "enabled": False if profile is None else bool(profile.get("enabled") is True),
        "wallet_authority_hash": None if profile is None else profile.get("wallet_authority_hash"),
        "expected_wallet_authority_hash": expected_wallet_authority_hash,
        "signer_registry_hash": None
        if profile is None or not isinstance(profile.get("signer_registry"), Mapping)
        else profile["signer_registry"].get("registry_hash"),
        "key_manager_hash": None
        if profile is None or not isinstance(profile.get("key_manager"), Mapping)
        else profile["key_manager"].get("manager_hash"),
        "active_signer_count": int(active_signer_count),
        "threshold": int(threshold),
        "key_ref_count": int(key_ref_count),
        "key_refs": list(key_refs or []),
        "active_signers": list(active_signers or []),
        "wallet_ux": dict(wallet_ux or {}),
        "proof_profile": dict(proof_profile or {}),
        "transaction_scope": dict(transaction_scope or {}),
        "not_claimed": list(_NOT_CLAIMED),
    }
