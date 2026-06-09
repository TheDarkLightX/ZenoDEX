"""Production-authority preflight for mounted ZenoOracle services.

This module does not grant production authority by configuration alone. It
checks the local authority profile that would let a UI or operator process tell
the difference between a devnet/local Oracle service and a production-authorized
Oracle surface.
"""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_key_manager import KEY_MANAGER_SCHEMA_V0, KEY_STATUS_ACTIVE, KeyRef
from src.integration.zeno_ledger_signer_registry import validate_signer_registry_v0, verify_signature_quorum_v0
from src.integration.zeno_ledger_v0 import hash_v0


ORACLE_AUTHORITY_PROFILE_SCHEMA_V1 = "zenodex/oracle-production-authority-profile/v1"
ORACLE_AUTHORITY_STATUS_SCHEMA_V1 = "zenodex/oracle-production-authority-status/v1"
ORACLE_AUTHORITY_EXERCISE_SCHEMA_V1 = "zenodex/oracle-production-authority-exercise/v1"
ORACLE_AUTHORITY_EXERCISE_STATUS_SCHEMA_V1 = "zenodex/oracle-production-authority-exercise-status/v1"
ORACLE_AUTHORITY_PAYLOAD_KIND = "oracle_authority_profile"

_REQUIRED_WALLET_UX_FLAGS = (
    "external_signer_required",
    "key_manager_required",
    "device_approval_required",
)
_REQUIRED_PROOF_FLAGS = (
    "zk_or_proof_required",
    "oracle_receipt_replay_required",
)
_NOT_CLAIMED = (
    "does_not_claim_true_market_price",
    "does_not_claim_source_honesty",
    "does_not_claim_tau_consensus_finality",
)
_EXERCISE_NOT_CLAIMED = (
    # Honesty non-claim: when public broadcast/settlement references are
    # supplied this path only format-checks them (non-empty / presence). It
    # does NOT verify them against a real chain (no RPC, no inclusion proof).
    # Presence of references therefore does NOT establish a chain-verified
    # public-testnet exercise.
    "public_testnet_broadcast_references_are_format_checked_not_chain_verified",
    "does_not_claim_chain_verified_public_testnet_exercise",
    "does_not_claim_true_market_price",
    "does_not_claim_tau_consensus_finality",
)
_NON_HASH_PROFILE_FIELDS = frozenset({"authority_hash", "signature_envelopes", "signature_quorum"})
_NON_HASH_EXERCISE_FIELDS = frozenset({"exercise_hash"})
_EXERCISE_NETWORKS = frozenset({"local", "testnet", "public_testnet"})


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
        raise ValueError(f"{name} must be a non-negative integer")
    return int(value)


def _body(profile: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(profile).items() if key not in _NON_HASH_PROFILE_FIELDS}


def oracle_authority_profile_hash_v1(profile: Mapping[str, Any]) -> str:
    return hash_v0("zeno_oracle_authority_profile_v1", _body(profile))


def _exercise_body(exercise: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(exercise).items() if key not in _NON_HASH_EXERCISE_FIELDS}


def oracle_authority_exercise_hash_v1(exercise: Mapping[str, Any]) -> str:
    return hash_v0("zeno_oracle_authority_exercise_v1", _exercise_body(exercise))


def _exercise_receipt_binding_hash(exercise: Mapping[str, Any]) -> str:
    body = {
        "chain_id": exercise.get("chain_id"),
        "authority_id": exercise.get("authority_id"),
        "target_network": exercise.get("target_network"),
        "current_epoch": exercise.get("current_epoch"),
        "operator_service_url": exercise.get("operator_service_url"),
        "query_id": exercise.get("query_id"),
        "report_id": exercise.get("report_id"),
        "aggregate_id": exercise.get("aggregate_id"),
        "read_id": exercise.get("read_id"),
        "authorization_id": exercise.get("authorization_id"),
        "reward_receipt_id": exercise.get("reward_receipt_id"),
    }
    return hash_v0("zeno_oracle_authority_exercise_receipt_binding_v1", body)


def _public_testnet_evidence_binding_hash(exercise: Mapping[str, Any]) -> str | None:
    public_broadcast_reference = exercise.get("public_broadcast_reference")
    public_settlement_reference = exercise.get("public_settlement_reference")
    if not isinstance(public_broadcast_reference, str) or not public_broadcast_reference:
        return None
    if not isinstance(public_settlement_reference, str) or not public_settlement_reference:
        return None
    body = {
        "chain_id": exercise.get("chain_id"),
        "authority_id": exercise.get("authority_id"),
        "target_network": exercise.get("target_network"),
        "public_broadcast_reference": public_broadcast_reference,
        "public_settlement_reference": public_settlement_reference,
    }
    return hash_v0("zeno_oracle_authority_public_testnet_evidence_binding_v1", body)


def build_oracle_authority_exercise_v1(
    *,
    chain_id: str,
    authority_id: str,
    target_network: str,
    current_epoch: int,
    operator_service_url: str,
    query_id: str,
    report_id: str,
    aggregate_id: str,
    read_id: str,
    authorization_id: str,
    reward_receipt_id: str,
    public_broadcast_reference: str | None = None,
    public_settlement_reference: str | None = None,
) -> dict[str, Any]:
    body = {
        "schema": ORACLE_AUTHORITY_EXERCISE_SCHEMA_V1,
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "target_network": _require_nonempty_str(target_network, name="target_network"),
        "current_epoch": _require_nonnegative_int(current_epoch, name="current_epoch"),
        "operator_service_url": _require_nonempty_str(operator_service_url, name="operator_service_url"),
        "query_id": _require_nonempty_str(query_id, name="query_id"),
        "report_id": _require_nonempty_str(report_id, name="report_id"),
        "aggregate_id": _require_nonempty_str(aggregate_id, name="aggregate_id"),
        "read_id": _require_nonempty_str(read_id, name="read_id"),
        "authorization_id": _require_nonempty_str(authorization_id, name="authorization_id"),
        "reward_receipt_id": _require_nonempty_str(reward_receipt_id, name="reward_receipt_id"),
        "public_broadcast_reference": None if public_broadcast_reference is None else _require_nonempty_str(public_broadcast_reference, name="public_broadcast_reference"),
        "public_settlement_reference": None if public_settlement_reference is None else _require_nonempty_str(public_settlement_reference, name="public_settlement_reference"),
    }
    return {**body, "exercise_hash": oracle_authority_exercise_hash_v1(body)}


def build_oracle_authority_profile_v1(
    *,
    authority_id: str,
    chain_id: str,
    stage: str,
    enabled: bool,
    key_manager: Mapping[str, Any],
    signer_registry: Mapping[str, Any],
    wallet_ux: Mapping[str, Any],
    proof_profile: Mapping[str, Any],
    signature_envelopes: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    body = {
        "schema": ORACLE_AUTHORITY_PROFILE_SCHEMA_V1,
        "authority_id": _require_nonempty_str(authority_id, name="authority_id"),
        "chain_id": _require_nonempty_str(chain_id, name="chain_id"),
        "stage": _require_nonempty_str(stage, name="stage"),
        "enabled": bool(enabled),
        "key_manager": dict(_require_mapping(key_manager, name="key_manager")),
        "signer_registry": dict(_require_mapping(signer_registry, name="signer_registry")),
        "wallet_ux": dict(_require_mapping(wallet_ux, name="wallet_ux")),
        "proof_profile": dict(_require_mapping(proof_profile, name="proof_profile")),
    }
    profile = {**body, "authority_hash": oracle_authority_profile_hash_v1(body)}
    if signature_envelopes is not None:
        profile["signature_envelopes"] = [
            dict(_require_mapping(envelope, name=f"signature_envelopes[{index}]"))
            for index, envelope in enumerate(signature_envelopes)
        ]
    return profile


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


def _signer_entries(signer_registry: Mapping[str, Any], gaps: list[str]) -> tuple[list[Mapping[str, Any]], int]:
    try:
        validate_signer_registry_v0(signer_registry)
    except Exception as exc:
        gaps.append(f"signer registry invalid: {exc}")
        return [], 0

    if signer_registry.get("payload_kind") != ORACLE_AUTHORITY_PAYLOAD_KIND:
        gaps.append("signer registry payload_kind is not oracle_authority_profile")

    threshold_obj = signer_registry.get("threshold")
    threshold = int(threshold_obj) if isinstance(threshold_obj, int) and not isinstance(threshold_obj, bool) else 0
    if threshold < 2:
        gaps.append("active signer threshold must be at least 2")

    raw_entries = signer_registry.get("signers")
    if not isinstance(raw_entries, list):
        gaps.append("signer registry signers must be a list")
        return [], threshold
    active = [
        entry
        for entry in raw_entries
        if isinstance(entry, Mapping) and entry.get("status") == KEY_STATUS_ACTIVE
    ]
    if len(active) < 2:
        gaps.append("at least two active authority signers are required")
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


def _signature_quorum_summary(report: Mapping[str, Any]) -> dict[str, Any]:
    accepted = report.get("accepted_signatures")
    accepted_signatures = accepted if isinstance(accepted, list) else []
    return {
        "registry_hash": report.get("registry_hash"),
        "payload_kind": report.get("payload_kind"),
        "payload_hash": report.get("payload_hash"),
        "threshold": int(report.get("threshold", 0)) if isinstance(report.get("threshold"), int) else 0,
        "accepted_weight": int(report.get("accepted_weight", 0)) if isinstance(report.get("accepted_weight"), int) else 0,
        "accepted_signature_count": len(accepted_signatures),
        "accepted_signatures": [
            {
                "signer_id": str(item.get("signer_id", "")) if isinstance(item, Mapping) else "",
                "key_id": str(item.get("key_id", "")) if isinstance(item, Mapping) else "",
                "weight": int(item.get("weight", 0)) if isinstance(item, Mapping) and isinstance(item.get("weight"), int) else 0,
                "envelope_hash": item.get("envelope_hash") if isinstance(item, Mapping) else None,
            }
            for item in accepted_signatures
        ],
        "quorum_report_hash": report.get("quorum_report_hash"),
    }


def _validate_signature_quorum(
    *,
    profile: Mapping[str, Any],
    signer_registry: Mapping[str, Any],
    expected_authority_hash: str,
    gaps: list[str],
) -> dict[str, Any] | None:
    raw_envelopes = profile.get("signature_envelopes")
    if not isinstance(raw_envelopes, list) or not raw_envelopes:
        gaps.append("oracle production authority signature_envelopes must be a non-empty list")
        return None
    envelopes: list[Mapping[str, Any]] = []
    for index, raw_envelope in enumerate(raw_envelopes):
        try:
            envelopes.append(_require_mapping(raw_envelope, name=f"signature_envelopes[{index}]"))
        except Exception as exc:
            gaps.append(f"oracle production authority signature envelope {index} invalid: {exc}")
    if not envelopes:
        return None
    try:
        report = verify_signature_quorum_v0(
            registry=signer_registry,
            payload_kind=ORACLE_AUTHORITY_PAYLOAD_KIND,
            payload_hash=expected_authority_hash,
            envelopes=envelopes,
        )
    except Exception as exc:
        gaps.append(f"oracle production authority signature quorum invalid: {exc}")
        return None
    return _signature_quorum_summary(report)


def _public_flag_profile(profile: Mapping[str, Any], flags: tuple[str, ...]) -> dict[str, bool]:
    return {flag: profile.get(flag) is True for flag in flags}


def evaluate_oracle_authority_profile_v1(profile: Mapping[str, Any] | None) -> dict[str, Any]:
    gaps: list[str] = []
    if profile is None:
        gaps.append("oracle production authority profile is missing")
        return _status(
            ok=False,
            production_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            signature_count=0,
            key_refs=[],
            active_signers=[],
            signature_quorum=None,
            wallet_ux={},
            proof_profile={},
        )

    try:
        obj = _require_mapping(profile, name="profile")
    except Exception as exc:
        gaps.append(f"oracle production authority profile invalid: {exc}")
        return _status(
            ok=False,
            production_authority=False,
            readiness_gaps=gaps,
            profile=None,
            active_signer_count=0,
            threshold=0,
            key_ref_count=0,
            signature_count=0,
            key_refs=[],
            active_signers=[],
            signature_quorum=None,
            wallet_ux={},
            proof_profile={},
        )

    if obj.get("schema") != ORACLE_AUTHORITY_PROFILE_SCHEMA_V1:
        gaps.append("oracle production authority profile schema mismatch")
    if not isinstance(obj.get("enabled"), bool) or obj.get("enabled") is not True:
        gaps.append("oracle production authority profile is not enabled")
    if obj.get("stage") != "production":
        gaps.append("oracle production authority profile stage must be production")

    try:
        _require_nonempty_str(obj.get("authority_id"), name="authority_id")
    except Exception as exc:
        gaps.append(str(exc))
    try:
        _require_nonempty_str(obj.get("chain_id"), name="chain_id")
    except Exception as exc:
        gaps.append(str(exc))

    expected_hash = oracle_authority_profile_hash_v1(obj)
    if obj.get("authority_hash") != expected_hash:
        gaps.append("oracle production authority profile hash mismatch")

    key_refs: dict[str, KeyRef] = {}
    try:
        key_manager = _require_mapping(obj.get("key_manager"), name="key_manager")
        key_refs = _validate_key_manager_public(key_manager, gaps)
    except Exception as exc:
        gaps.append(f"key manager invalid: {exc}")

    active_signers: list[Mapping[str, Any]] = []
    threshold = 0
    signer_registry: Mapping[str, Any] | None = None
    try:
        signer_registry = _require_mapping(obj.get("signer_registry"), name="signer_registry")
        active_signers, threshold = _signer_entries(signer_registry, gaps)
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

    signature_quorum: dict[str, Any] | None = None
    if signer_registry is not None:
        signature_quorum = _validate_signature_quorum(
            profile=obj,
            signer_registry=signer_registry,
            expected_authority_hash=expected_hash,
            gaps=gaps,
        )

    production_authority = not gaps
    return _status(
        ok=production_authority,
        production_authority=production_authority,
        readiness_gaps=gaps,
        profile=obj,
        active_signer_count=len(active_signers),
        threshold=threshold,
        key_ref_count=len(key_refs),
        signature_count=0 if signature_quorum is None else int(signature_quorum["accepted_signature_count"]),
        expected_authority_hash=expected_hash,
        key_refs=_key_ref_summaries(key_refs),
        active_signers=_active_signer_summaries(active_signers),
        signature_quorum=signature_quorum,
        wallet_ux=wallet_ux_summary,
        proof_profile=proof_profile_summary,
    )


def _status(
    *,
    ok: bool,
    production_authority: bool,
    readiness_gaps: list[str],
    profile: Mapping[str, Any] | None,
    active_signer_count: int,
    threshold: int,
    key_ref_count: int,
    signature_count: int,
    expected_authority_hash: str | None = None,
    key_refs: list[dict[str, Any]] | None = None,
    active_signers: list[dict[str, Any]] | None = None,
    signature_quorum: Mapping[str, Any] | None = None,
    wallet_ux: Mapping[str, Any] | None = None,
    proof_profile: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema": ORACLE_AUTHORITY_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "production_authority": bool(production_authority),
        "status": "ready" if production_authority else "blocked",
        "readiness_gaps": list(readiness_gaps),
        "authority_id": None if profile is None else profile.get("authority_id"),
        "chain_id": None if profile is None else profile.get("chain_id"),
        "stage": None if profile is None else profile.get("stage"),
        "enabled": False if profile is None else bool(profile.get("enabled") is True),
        "authority_hash": None if profile is None else profile.get("authority_hash"),
        "expected_authority_hash": expected_authority_hash,
        "signer_registry_hash": None
        if profile is None or not isinstance(profile.get("signer_registry"), Mapping)
        else profile["signer_registry"].get("registry_hash"),
        "key_manager_hash": None
        if profile is None or not isinstance(profile.get("key_manager"), Mapping)
        else profile["key_manager"].get("manager_hash"),
        "active_signer_count": int(active_signer_count),
        "threshold": int(threshold),
        "key_ref_count": int(key_ref_count),
        "signature_count": int(signature_count),
        "key_refs": list(key_refs or []),
        "active_signers": list(active_signers or []),
        "signature_quorum": dict(signature_quorum or {}),
        "wallet_ux": dict(wallet_ux or {}),
        "proof_profile": dict(proof_profile or {}),
        "not_claimed": list(_NOT_CLAIMED),
    }


def _exercise_status(
    *,
    ok: bool,
    errors: list[str],
    exercise: Mapping[str, Any] | None,
    authority_status: Mapping[str, Any] | None,
    public_testnet_evidence_present: bool,
) -> dict[str, Any]:
    body = {
        "schema": ORACLE_AUTHORITY_EXERCISE_STATUS_SCHEMA_V1,
        "ok": bool(ok),
        "authority_exercised": bool(ok),
        "public_testnet_evidence_present": bool(public_testnet_evidence_present),
        "public_testnet_exercised": bool(ok and public_testnet_evidence_present),
        "status": "ready" if ok else "blocked",
        "errors": list(errors),
        "exercise_hash": None if exercise is None else oracle_authority_exercise_hash_v1(exercise),
        "target_network": None if exercise is None else exercise.get("target_network"),
        "chain_id": None if exercise is None else exercise.get("chain_id"),
        "authority_id": None if exercise is None else exercise.get("authority_id"),
        "current_epoch": None if exercise is None else exercise.get("current_epoch"),
        "query_id": None if exercise is None else exercise.get("query_id"),
        "report_id": None if exercise is None else exercise.get("report_id"),
        "aggregate_id": None if exercise is None else exercise.get("aggregate_id"),
        "read_id": None if exercise is None else exercise.get("read_id"),
        "authorization_id": None if exercise is None else exercise.get("authorization_id"),
        "reward_receipt_id": None if exercise is None else exercise.get("reward_receipt_id"),
        "public_broadcast_reference": None if exercise is None else exercise.get("public_broadcast_reference"),
        "public_settlement_reference": None if exercise is None else exercise.get("public_settlement_reference"),
        "receipt_binding_hash": None if exercise is None else _exercise_receipt_binding_hash(exercise),
        "public_testnet_evidence_binding_hash": (
            None if exercise is None else _public_testnet_evidence_binding_hash(exercise)
        ),
        "authority_hash": None if authority_status is None else authority_status.get("authority_hash"),
        "authority_status_hash": None if authority_status is None else hash_v0("zeno_oracle_authority_status_ref_v1", dict(authority_status)),
        "not_claimed": list(_EXERCISE_NOT_CLAIMED),
    }
    return {**body, "status_hash": hash_v0("zeno_oracle_authority_exercise_status_v1", body)}


def evaluate_oracle_authority_exercise_v1(
    profile: Mapping[str, Any] | None,
    exercise: Mapping[str, Any] | None,
    *,
    expected_chain_id: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    authority_status = evaluate_oracle_authority_profile_v1(profile)
    if exercise is None:
        return _exercise_status(
            ok=False,
            errors=["oracle production authority exercise is missing"],
            exercise=None,
            authority_status=authority_status,
            public_testnet_evidence_present=False,
        )
    try:
        exercise_obj = _require_mapping(exercise, name="authority_exercise")
    except Exception as exc:
        return _exercise_status(
            ok=False,
            errors=[f"oracle production authority exercise invalid: {exc}"],
            exercise=exercise if isinstance(exercise, Mapping) else None,
            authority_status=authority_status,
            public_testnet_evidence_present=False,
        )
    if authority_status.get("production_authority") is not True:
        errors.append("oracle production authority profile is not ready")
        errors.extend(str(gap) for gap in authority_status.get("readiness_gaps", []))
    try:
        if exercise_obj.get("schema") != ORACLE_AUTHORITY_EXERCISE_SCHEMA_V1:
            errors.append("oracle production authority exercise schema mismatch")
        chain_id = _require_nonempty_str(exercise_obj.get("chain_id"), name="chain_id")
        authority_id = _require_nonempty_str(exercise_obj.get("authority_id"), name="authority_id")
        target_network = _require_nonempty_str(exercise_obj.get("target_network"), name="target_network")
        current_epoch = _require_nonnegative_int(exercise_obj.get("current_epoch"), name="current_epoch")
        operator_service_url = _require_nonempty_str(exercise_obj.get("operator_service_url"), name="operator_service_url")
        query_id = _require_nonempty_str(exercise_obj.get("query_id"), name="query_id")
        report_id = _require_nonempty_str(exercise_obj.get("report_id"), name="report_id")
        aggregate_id = _require_nonempty_str(exercise_obj.get("aggregate_id"), name="aggregate_id")
        read_id = _require_nonempty_str(exercise_obj.get("read_id"), name="read_id")
        authorization_id = _require_nonempty_str(exercise_obj.get("authorization_id"), name="authorization_id")
        reward_receipt_id = _require_nonempty_str(exercise_obj.get("reward_receipt_id"), name="reward_receipt_id")
    except Exception as exc:
        errors.append(str(exc))
        return _exercise_status(
            ok=False,
            errors=errors,
            exercise=exercise_obj,
            authority_status=authority_status,
            public_testnet_evidence_present=False,
        )
    _ = current_epoch
    _ = operator_service_url
    _ = query_id
    _ = report_id
    _ = aggregate_id
    _ = read_id
    _ = authorization_id
    _ = reward_receipt_id
    if target_network not in _EXERCISE_NETWORKS:
        errors.append("target_network must be one of local, testnet, public_testnet")
    if expected_chain_id is not None and chain_id != expected_chain_id:
        errors.append("oracle production authority exercise chain_id mismatch")
    if chain_id != authority_status.get("chain_id"):
        errors.append("oracle production authority exercise profile chain_id mismatch")
    if authority_id != authority_status.get("authority_id"):
        errors.append("oracle production authority exercise authority_id mismatch")
    public_broadcast_reference = exercise_obj.get("public_broadcast_reference")
    public_settlement_reference = exercise_obj.get("public_settlement_reference")
    public_testnet_evidence_present = bool(
        isinstance(public_broadcast_reference, str)
        and public_broadcast_reference
        and isinstance(public_settlement_reference, str)
        and public_settlement_reference
    )
    if target_network == "public_testnet" and not public_testnet_evidence_present:
        errors.append("public testnet exercise requires public_broadcast_reference and public_settlement_reference")
    return _exercise_status(
        ok=not errors,
        errors=errors,
        exercise=exercise_obj,
        authority_status=authority_status,
        public_testnet_evidence_present=public_testnet_evidence_present,
    )
