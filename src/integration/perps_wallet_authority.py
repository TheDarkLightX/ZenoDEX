"""Production wallet-authority preflight for the mounted perps stream-8 lane.

This checks public key-manager, signer-registry, wallet UX, and proof posture
metadata. It does not custody keys, verify a hardware wallet, or prove perps
execution in a zkVM.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.zeno_key_manager import (
    KEY_MANAGER_SCHEMA_V0,
    KEY_STATUS_ACTIVE,
    KEY_STATUS_REVOKED,
    KeyRef,
    RecoveryGuardian,
    SECRET_FIELD_NAMES,
    SOCIAL_RECOVERY_POLICY_SCHEMA_V0,
    SocialRecoveryPolicy,
)
from src.integration.zeno_ledger_signer_registry import validate_signer_registry_v0
from src.integration.zeno_ledger_v0 import hash_v0


PERPS_WALLET_AUTHORITY_PROFILE_SCHEMA_V1 = "zenodex/perps-wallet-authority-profile/v1"
PERPS_WALLET_AUTHORITY_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-authority-status/v1"
PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1 = "zenodex/perps-wallet-recovery-exercise/v1"
PERPS_WALLET_RECOVERY_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/perps-wallet-recovery-exercise-status/v1"
PERPS_WALLET_AUTHORITY_PAYLOAD_KIND = "perps_wallet_authority_profile"

_REQUIRED_WALLET_UX_FLAGS = (
    "external_signer_required",
    "key_manager_required",
    "device_approval_required",
    "replay_protection_required",
    "recovery_policy_required",
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
    "does_not_claim_guardian_signature_verification",
    "does_not_claim_recovery_rotation_broadcast",
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_string_list(value: object, *, name: str) -> list[str]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            raise ValueError(f"{name}[{index}] must be a non-empty string")
        out.append(item)
    return out


def _reject_secret_fields(value: object, *, name: str = "payload") -> None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if str(key).lower() in SECRET_FIELD_NAMES:
                raise ValueError(f"{name} must not contain private key material")
            _reject_secret_fields(item, name=f"{name}.{key}")
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _reject_secret_fields(item, name=f"{name}[{index}]")


def _body(profile: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(profile).items() if key != "wallet_authority_hash"}


def perps_wallet_authority_profile_hash_v1(profile: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_authority_profile_v1", _body(profile))


def _recovery_exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key != "exercise_hash"}


def perps_wallet_recovery_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("perps_wallet_recovery_exercise_v1", _recovery_exercise_body(exercise))


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


def _validate_key_manager_public(
    key_manager: Mapping[str, Any],
    gaps: list[str],
) -> tuple[dict[str, KeyRef], list[Mapping[str, Any]]]:
    if key_manager.get("schema") != KEY_MANAGER_SCHEMA_V0:
        gaps.append("key manager schema mismatch")
        return {}, []

    key_refs_raw = key_manager.get("key_refs")
    recovery_policies_raw = key_manager.get("recovery_policies")
    if not isinstance(key_refs_raw, list):
        gaps.append("key manager key_refs must be a list")
        return {}, []
    if not isinstance(recovery_policies_raw, list):
        gaps.append("key manager recovery_policies must be a list")
        return {}, []

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
    return refs, recovery_policies_raw


def _validate_recovery_policies_public(
    *,
    recovery_policies_raw: list[Mapping[str, Any]],
    key_refs: Mapping[str, KeyRef],
    active_signers: list[Mapping[str, Any]],
    gaps: list[str],
) -> tuple[list[dict[str, Any]], int]:
    policies_by_id: dict[str, Mapping[str, Any]] = {}
    summaries: list[dict[str, Any]] = []
    for index, raw_policy in enumerate(recovery_policies_raw):
        policy = _require_mapping(raw_policy, name=f"recovery_policies[{index}]")
        if policy.get("schema") != SOCIAL_RECOVERY_POLICY_SCHEMA_V0:
            gaps.append(f"recovery policy {index} schema mismatch")
            continue
        policy_id = policy.get("policy_id")
        subject_key_id = policy.get("subject_key_id")
        threshold = policy.get("threshold")
        delay_epochs = policy.get("delay_epochs")
        guardians = policy.get("guardians")
        if not isinstance(policy_id, str) or not policy_id:
            gaps.append(f"recovery policy {index} policy_id must be a non-empty string")
            continue
        if policy_id in policies_by_id:
            gaps.append(f"duplicate recovery policy_id: {policy_id}")
            continue
        if not isinstance(subject_key_id, str) or not subject_key_id:
            gaps.append(f"recovery policy {policy_id} subject_key_id must be a non-empty string")
        elif subject_key_id not in key_refs:
            gaps.append(f"recovery policy {policy_id} subject key missing from key manager")
        if not isinstance(threshold, int) or isinstance(threshold, bool) or threshold <= 0:
            gaps.append(f"recovery policy {policy_id} threshold must be a positive int")
            threshold = 0
        if not isinstance(delay_epochs, int) or isinstance(delay_epochs, bool) or delay_epochs < 0:
            gaps.append(f"recovery policy {policy_id} delay_epochs must be a non-negative int")
            delay_epochs = 0
        if not isinstance(guardians, list) or not guardians:
            gaps.append(f"recovery policy {policy_id} guardians must be a non-empty list")
            guardians = []
        active_guardian_weight = 0
        guardian_ids: set[str] = set()
        for guardian_index, guardian_raw in enumerate(guardians):
            guardian = _require_mapping(guardian_raw, name=f"recovery_policies[{index}].guardians[{guardian_index}]")
            guardian_id = guardian.get("guardian_id")
            public_key = guardian.get("public_key")
            weight = guardian.get("weight")
            status = guardian.get("status")
            if not isinstance(guardian_id, str) or not guardian_id:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_index} guardian_id must be a non-empty string")
                continue
            if guardian_id in guardian_ids:
                gaps.append(f"recovery policy {policy_id} duplicate guardian_id: {guardian_id}")
            guardian_ids.add(guardian_id)
            if not isinstance(public_key, str) or not public_key:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} public_key must be a non-empty string")
            if not isinstance(weight, int) or isinstance(weight, bool) or weight <= 0:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} weight must be a positive int")
                weight = 0
            if status not in {KEY_STATUS_ACTIVE, KEY_STATUS_REVOKED}:
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} status must be active or revoked")
            if status == KEY_STATUS_ACTIVE:
                active_guardian_weight += int(weight)
            guardian_body = {
                "guardian_id": guardian.get("guardian_id"),
                "public_key": guardian.get("public_key"),
                "weight": guardian.get("weight"),
                "status": guardian.get("status"),
            }
            if guardian.get("guardian_hash") != hash_v0("zeno_recovery_guardian_v0", guardian_body):
                gaps.append(f"recovery policy {policy_id} guardian {guardian_id} hash mismatch")
        if isinstance(threshold, int) and threshold > active_guardian_weight:
            gaps.append(f"recovery policy {policy_id} threshold exceeds active guardian weight")
        policy_body = {
            "schema": policy.get("schema"),
            "policy_id": policy.get("policy_id"),
            "subject_key_id": policy.get("subject_key_id"),
            "threshold": policy.get("threshold"),
            "delay_epochs": policy.get("delay_epochs"),
            "guardians": guardians,
        }
        expected_policy_hash = hash_v0("zeno_social_recovery_policy_v0", policy_body)
        if policy.get("policy_hash") != expected_policy_hash:
            gaps.append(f"recovery policy {policy_id} hash mismatch")
        policies_by_id[policy_id] = policy
        summaries.append(
            {
                "policy_id": policy_id,
                "subject_key_id": subject_key_id,
                "threshold": int(threshold) if isinstance(threshold, int) else 0,
                "delay_epochs": int(delay_epochs) if isinstance(delay_epochs, int) else 0,
                "guardian_count": len(guardians),
                "active_guardian_weight": active_guardian_weight,
                "policy_hash": policy.get("policy_hash"),
            }
        )

    recoverable_active_key_ids: set[str] = set()
    for signer in active_signers:
        key_id = signer.get("key_id")
        if not isinstance(key_id, str) or not key_id:
            continue
        ref = key_refs.get(key_id)
        if ref is None:
            continue
        if ref.recovery_policy_id is None:
            gaps.append(f"active signer key_id {key_id} has no recovery_policy_id")
            continue
        policy = policies_by_id.get(ref.recovery_policy_id)
        if policy is None:
            gaps.append(f"active signer key_id {key_id} recovery policy missing")
            continue
        if policy.get("subject_key_id") != key_id:
            gaps.append(f"active signer key_id {key_id} recovery policy subject mismatch")
            continue
        recoverable_active_key_ids.add(key_id)

    return sorted(summaries, key=lambda item: str(item["policy_id"])), len(recoverable_active_key_ids)


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


def _social_recovery_policy_from_public_dict(policy: Mapping[str, Any]) -> SocialRecoveryPolicy:
    obj = _require_mapping(policy, name="recovery_policy")
    if obj.get("schema") != SOCIAL_RECOVERY_POLICY_SCHEMA_V0:
        raise ValueError("recovery policy schema mismatch")
    guardians_raw = obj.get("guardians")
    if not isinstance(guardians_raw, list):
        raise TypeError("recovery policy guardians must be a list")
    guardians: list[RecoveryGuardian] = []
    for index, raw in enumerate(guardians_raw):
        guardian = _require_mapping(raw, name=f"guardians[{index}]")
        guardians.append(
            RecoveryGuardian(
                guardian_id=_require_nonempty_str(guardian.get("guardian_id"), name="guardian_id"),
                public_key=_require_nonempty_str(guardian.get("public_key"), name="public_key"),
                weight=_require_nonnegative_int(guardian.get("weight"), name="weight"),
                status=_require_nonempty_str(guardian.get("status"), name="status"),
            )
        )
    policy_obj = SocialRecoveryPolicy(
        policy_id=_require_nonempty_str(obj.get("policy_id"), name="policy_id"),
        subject_key_id=_require_nonempty_str(obj.get("subject_key_id"), name="subject_key_id"),
        threshold=_require_nonnegative_int(obj.get("threshold"), name="threshold"),
        delay_epochs=_require_nonnegative_int(obj.get("delay_epochs"), name="delay_epochs"),
        guardians=tuple(guardians),
    )
    if dict(obj) != policy_obj.public_dict():
        raise ValueError("recovery policy binding mismatch")
    return policy_obj


def _recovery_exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    wallet_authority_hash: str | None,
    evaluation: Mapping[str, Any] | None,
) -> dict[str, Any]:
    body = {
        "schema": PERPS_WALLET_RECOVERY_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "recovery_exercise_ready": bool(ok),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "wallet_authority_hash": wallet_authority_hash,
        "exercise_hash": None if exercise is None else perps_wallet_recovery_exercise_hash_v1(exercise),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "subject_key_id": None if exercise is None else exercise.get("subject_key_id"),
        "policy_id": None if exercise is None else exercise.get("policy_id"),
        "requested_at_epoch": None if exercise is None else exercise.get("requested_at_epoch"),
        "current_epoch": None if exercise is None else exercise.get("current_epoch"),
        "evaluation": None if evaluation is None else dict(evaluation),
        "evaluation_hash": None if evaluation is None else evaluation.get("evaluation_hash"),
        "not_claimed": [
            "does_not_claim_guardian_signature_verification",
            "does_not_claim_hardware_wallet_custody",
            "does_not_claim_recovery_rotation_broadcast",
        ],
    }
    return {**body, "status_hash": hash_v0("perps_wallet_recovery_exercise_status_v1", body)}


def evaluate_perps_wallet_recovery_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    if exercise is None:
        return _recovery_exercise_status(
            ok=False,
            errors=["perps wallet recovery exercise is missing"],
            exercise=None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            evaluation=None,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="recovery_exercise")
        _reject_secret_fields(exercise_obj, name="recovery_exercise")
    except Exception as exc:
        return _recovery_exercise_status(
            ok=False,
            errors=[f"perps wallet recovery exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            wallet_authority_hash=None if profile is None else profile.get("wallet_authority_hash"),
            evaluation=None,
        )
    if profile is None:
        return _recovery_exercise_status(
            ok=False,
            errors=["perps wallet authority profile is missing"],
            exercise=exercise_obj,
            wallet_authority_hash=None,
            evaluation=None,
        )

    authority_status = evaluate_perps_wallet_authority_profile_v1(profile, expected_chain_id=expected_chain_id)
    if authority_status["production_wallet_authority"] is not True:
        errors.append("perps wallet authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))

    try:
        if exercise_obj.get("schema") != PERPS_WALLET_RECOVERY_EXERCISE_SCHEMA_V1:
            errors.append("perps wallet recovery exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        subject_key_id = _require_nonempty_str(exercise_obj.get("subject_key_id"), name="subject_key_id")
        policy_id = _require_nonempty_str(exercise_obj.get("policy_id"), name="policy_id")
        requested_at_epoch = _require_nonnegative_int(exercise_obj.get("requested_at_epoch"), name="requested_at_epoch")
        current_epoch = _require_nonnegative_int(exercise_obj.get("current_epoch"), name="current_epoch")
        approvals = _require_string_list(exercise_obj.get("approvals"), name="approvals")
    except Exception as exc:
        errors.append(str(exc))
        return _recovery_exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            wallet_authority_hash=profile.get("wallet_authority_hash"),
            evaluation=None,
        )
    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("perps wallet recovery exercise chain_id mismatch")
    if chain_id != profile.get("chain_id"):
        errors.append("perps wallet recovery exercise profile chain_id mismatch")
    if authority_id != profile.get("authority_id"):
        errors.append("perps wallet recovery exercise authority_id mismatch")

    active_key_ids = {str(item.get("key_id")) for item in authority_status.get("active_signers", []) if isinstance(item, Mapping)}
    if subject_key_id not in active_key_ids:
        errors.append("perps wallet recovery exercise subject key is not active")

    evaluation: Mapping[str, Any] | None = None
    try:
        key_manager = _require_mapping(profile.get("key_manager"), name="key_manager")
        policies_raw = key_manager.get("recovery_policies")
        if not isinstance(policies_raw, list):
            raise TypeError("key manager recovery_policies must be a list")
        matching = [
            _social_recovery_policy_from_public_dict(_require_mapping(raw, name="recovery_policy"))
            for raw in policies_raw
            if isinstance(raw, Mapping) and raw.get("policy_id") == policy_id
        ]
        if len(matching) != 1:
            raise ValueError("recovery policy not found")
        policy = matching[0]
        if policy.subject_key_id != subject_key_id:
            errors.append("perps wallet recovery exercise policy subject mismatch")
        evaluation = policy.evaluate(
            approvals=approvals,
            requested_at_epoch=requested_at_epoch,
            current_epoch=current_epoch,
        )
        if evaluation.get("ok") is not True:
            errors.append("recovery_policy_not_satisfied")
    except Exception as exc:
        errors.append(f"recovery policy evaluation failed: {exc}")

    return _recovery_exercise_status(
        ok=not errors and evaluation is not None and evaluation.get("ok") is True,
        errors=errors,
        exercise=exercise_obj,
        wallet_authority_hash=profile.get("wallet_authority_hash"),
        evaluation=evaluation,
    )


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
            recovery_policy_count=0,
            recoverable_active_key_count=0,
            key_refs=[],
            active_signers=[],
            recovery_policies=[],
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
            recovery_policy_count=0,
            recoverable_active_key_count=0,
            key_refs=[],
            active_signers=[],
            recovery_policies=[],
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
    recovery_policies_raw: list[Mapping[str, Any]] = []
    try:
        key_manager = _require_mapping(obj.get("key_manager"), name="key_manager")
        key_refs, recovery_policies_raw = _validate_key_manager_public(key_manager, gaps)
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

    recovery_policy_summaries: list[dict[str, Any]] = []
    recoverable_active_key_count = 0
    try:
        recovery_policy_summaries, recoverable_active_key_count = _validate_recovery_policies_public(
            recovery_policies_raw=recovery_policies_raw,
            key_refs=key_refs,
            active_signers=active_signers,
            gaps=gaps,
        )
    except Exception as exc:
        gaps.append(f"recovery policies invalid: {exc}")

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
        recovery_policy_count=len(recovery_policy_summaries),
        recoverable_active_key_count=recoverable_active_key_count,
        expected_wallet_authority_hash=expected_hash,
        key_refs=_key_ref_summaries(key_refs),
        active_signers=_active_signer_summaries(active_signers),
        recovery_policies=recovery_policy_summaries,
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
    recovery_policy_count: int,
    recoverable_active_key_count: int,
    expected_wallet_authority_hash: str | None = None,
    key_refs: list[dict[str, Any]] | None = None,
    active_signers: list[dict[str, Any]] | None = None,
    recovery_policies: list[dict[str, Any]] | None = None,
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
        "recovery_policy_count": int(recovery_policy_count),
        "recoverable_active_key_count": int(recoverable_active_key_count),
        "key_refs": list(key_refs or []),
        "active_signers": list(active_signers or []),
        "recovery_policies": list(recovery_policies or []),
        "wallet_ux": dict(wallet_ux or {}),
        "proof_profile": dict(proof_profile or {}),
        "transaction_scope": dict(transaction_scope or {}),
        "not_claimed": list(_NOT_CLAIMED),
    }
