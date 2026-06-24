"""Production authority gate for governance and key-management actions."""

from __future__ import annotations

from typing import Any, Mapping, Sequence, cast

from src.integration.zeno_key_manager_v0 import (
    BACKEND_HARDWARE_WALLET_PLACEHOLDER,
    BACKEND_HSM_PLACEHOLDER,
    BACKEND_MPC_PLACEHOLDER,
    BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE,
    BACKEND_THRESHOLD_BLS_LOCAL,
    KeyBackendDescriptor,
)
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zenodex_external_threshold_bls import (
    APPROVED_EXTERNAL_THRESHOLD_BLS_PROVIDER_STACKS_V0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x


GOVERNANCE_AUTHORITY_RECEIPT_SCHEMA_V0 = "zenodex/governance_authority/receipt/v0"
GOVERNANCE_ACTION_PAYLOAD_KIND_V0 = "governance_action"

PROHIBITED_PRODUCTION_BACKEND_KINDS_V0 = frozenset(
    {
        BACKEND_HARDWARE_WALLET_PLACEHOLDER,
        BACKEND_HSM_PLACEHOLDER,
        BACKEND_MPC_PLACEHOLDER,
    }
)
REFERENCE_ONLY_PRODUCTION_BACKEND_KINDS_V0 = frozenset({BACKEND_THRESHOLD_BLS_LOCAL})
_MAX_GOVERNANCE_ERROR_CHARS = 512


def _safe_governance_error(exc: Exception) -> str:
    if isinstance(exc, (ValueError, TypeError, KeyError)):
        msg = str(exc)
    else:
        msg = f"internal error: {type(exc).__name__}"
    msg = " ".join((msg or "").split())
    if len(msg) > _MAX_GOVERNANCE_ERROR_CHARS:
        msg = msg[:_MAX_GOVERNANCE_ERROR_CHARS]
    return msg or "internal error"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def governance_action_payload_hash_v0(action: Mapping[str, Any]) -> str:
    """Return the canonical payload hash signers bind for a governance action."""

    obj = _require_mapping(action, name="action")
    return hash_v0("zenodex_governance_action_payload_v0", dict(obj))


def _normalize_backend_descriptor(raw: object, *, name: str) -> tuple[dict[str, Any] | None, str | None]:
    try:
        if isinstance(raw, KeyBackendDescriptor):
            return raw.public_dict(), None
        obj = _require_mapping(raw, name=name)
        descriptor = KeyBackendDescriptor(
            key_id=_require_str(obj.get("key_id"), name=f"{name}.key_id"),
            backend_kind=_require_str(obj.get("backend_kind"), name=f"{name}.backend_kind"),
            backend_id=_require_str(obj.get("backend_id"), name=f"{name}.backend_id"),
            policy_hash=_require_str(obj.get("policy_hash"), name=f"{name}.policy_hash"),
            active=bool(obj.get("active")),
            no_raw_private_key_exposure=bool(obj.get("no_raw_private_key_exposure")),
            metadata=_require_mapping(obj.get("metadata", {}), name=f"{name}.metadata"),
        )
        expected = descriptor.public_dict()
        if dict(obj) != expected:
            return None, f"{name}_binding_invalid"
        return expected, None
    except (TypeError, ValueError) as exc:
        return None, f"{name}_invalid:{_safe_governance_error(exc)}"


def _tau_policy_receipt_hash(receipt: object, *, production_mode: bool) -> tuple[str | None, list[str]]:
    errors: list[str] = []
    try:
        obj = _require_mapping(receipt, name="tau_policy_receipt")
        if obj.get("ok") is not True:
            errors.append("tau_policy_receipt_not_ok")
        if production_mode and "production_security_claim" in obj and obj.get("production_security_claim") is not True:
            errors.append("tau_policy_receipt_not_production_claim")
        root = obj.get("receipt_hash") if isinstance(obj.get("receipt_hash"), str) else obj.get("policy_hash")
        if root is None:
            errors.append("tau_policy_receipt_hash_missing")
            return None, errors
        return _require_root(root, name="tau_policy_receipt.hash"), errors
    except (TypeError, ValueError) as exc:
        return None, [*errors, f"tau_policy_receipt_invalid:{_safe_governance_error(exc)}"]


def _normalize_evidence_claims(
    claims: object,
    *,
    required_claims: frozenset[str],
    production_mode: bool,
) -> tuple[list[dict[str, Any]], list[str]]:
    errors: list[str] = []
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    if not isinstance(claims, Sequence) or isinstance(claims, (str, bytes, bytearray)):
        return [], ["evidence_claims_must_be_sequence"]
    for index, raw in enumerate(claims):
        try:
            obj = _require_mapping(raw, name=f"evidence_claims[{index}]")
            claim_kind = _require_str(obj.get("claim_kind"), name=f"evidence_claims[{index}].claim_kind").lower()
            if claim_kind in seen:
                errors.append(f"duplicate_evidence_claim:{claim_kind}")
            seen.add(claim_kind)
            ok = obj.get("ok") is True
            placeholder = obj.get("placeholder") is True
            if not ok:
                errors.append(f"evidence_claim_not_ok:{claim_kind}")
            if production_mode and placeholder:
                errors.append(f"production_placeholder_evidence_claim:{claim_kind}")
            if production_mode and "production_security_claim" in obj and obj.get("production_security_claim") is not True:
                errors.append(f"evidence_claim_not_production_claim:{claim_kind}")
            evidence_hash = _require_root(obj.get("evidence_hash"), name=f"evidence_claims[{index}].evidence_hash")
            normalized.append(
                {
                    "claim_kind": claim_kind,
                    "evidence_hash": evidence_hash,
                    "ok": ok,
                    "placeholder": placeholder,
                    "production_security_claim": obj.get("production_security_claim") is True,
                }
            )
        except (TypeError, ValueError) as exc:
            errors.append(f"evidence_claim_invalid:{index}:{_safe_governance_error(exc)}")
    for claim_kind in sorted(required_claims):
        if claim_kind not in seen:
            errors.append(f"required_evidence_claim_missing:{claim_kind}")
    normalized.sort(key=lambda item: (str(item["claim_kind"]), str(item["evidence_hash"])))
    return normalized, errors


def evaluate_governance_authority_v0(
    *,
    action_id: str,
    payload_kind: str,
    payload_hash: str,
    registry: Mapping[str, Any],
    signature_envelopes: Sequence[Mapping[str, Any]],
    current_epoch: int,
    proposal_epoch: int,
    min_delay_epochs: int,
    tau_policy_receipt: Mapping[str, Any],
    backend_descriptors: Sequence[KeyBackendDescriptor | Mapping[str, Any]],
    evidence_claims: Sequence[Mapping[str, Any]] = (),
    required_evidence_claims: Sequence[str] = (),
    production_mode: bool = True,
) -> dict[str, Any]:
    """Evaluate whether a governance action has production-grade authority evidence."""

    errors: list[str] = []
    normalized_action_id = ""
    normalized_payload_kind = ""
    normalized_payload_hash = ""
    normalized_current_epoch = -1
    normalized_proposal_epoch = -1
    normalized_min_delay = -1
    try:
        normalized_action_id = _require_str(action_id, name="action_id")
        normalized_payload_kind = _require_str(payload_kind, name="payload_kind")
        normalized_payload_hash = _require_root(payload_hash, name="payload_hash")
        normalized_current_epoch = _require_nonnegative_int(current_epoch, name="current_epoch")
        normalized_proposal_epoch = _require_nonnegative_int(proposal_epoch, name="proposal_epoch")
        normalized_min_delay = _require_nonnegative_int(min_delay_epochs, name="min_delay_epochs")
        if normalized_current_epoch < normalized_proposal_epoch + normalized_min_delay:
            errors.append("governance_timelock_not_elapsed")
    except (TypeError, ValueError) as exc:
        errors.append(f"governance_action_invalid:{_safe_governance_error(exc)}")

    sorted_envelopes: list[Mapping[str, Any]] = []
    signature_envelopes_obj: object = signature_envelopes
    if not isinstance(signature_envelopes_obj, Sequence) or isinstance(
        signature_envelopes_obj,
        (str, bytes, bytearray),
    ):
        errors.append("signature_envelopes_must_be_sequence")
    else:
        signature_envelope_seq = cast(Sequence[Mapping[str, Any]], signature_envelopes_obj)
        sorted_envelopes = sorted(
            signature_envelope_seq,
            key=lambda item: (
                str(item.get("signer_id")) if isinstance(item, Mapping) else "",
                str(item.get("key_id")) if isinstance(item, Mapping) else "",
                str(item.get("envelope_hash")) if isinstance(item, Mapping) else "",
            ),
        )

    quorum_report: dict[str, Any] | None = None
    if normalized_payload_kind and normalized_payload_hash and sorted_envelopes:
        try:
            quorum_report = verify_signature_quorum_v0(
                registry=registry,
                payload_kind=normalized_payload_kind,
                payload_hash=normalized_payload_hash,
                envelopes=sorted_envelopes,
            )
        except (TypeError, ValueError) as exc:
            errors.append(f"signature_quorum_invalid:{_safe_governance_error(exc)}")
    # Fail-closed: a governance action without a verified signature quorum has no
    # authority. Without this check an empty envelope list skipped quorum
    # verification entirely and the receipt could report ok=True with zero
    # signatures.
    if quorum_report is None and not any(
        str(error).startswith("signature_quorum_invalid") for error in errors
    ):
        errors.append("signature_quorum_missing")

    tau_hash, tau_errors = _tau_policy_receipt_hash(tau_policy_receipt, production_mode=production_mode)
    errors.extend(tau_errors)

    backend_public: list[dict[str, Any]] = []
    external_threshold_bls_evidence_hashes: set[str] = set()
    if not isinstance(backend_descriptors, Sequence) or isinstance(backend_descriptors, (str, bytes, bytearray)):
        errors.append("backend_descriptors_must_be_sequence")
    else:
        if production_mode and not backend_descriptors:
            errors.append("backend_descriptors_required")
        for index, raw in enumerate(backend_descriptors):
            descriptor, error = _normalize_backend_descriptor(raw, name=f"backend_descriptors[{index}]")
            if error is not None or descriptor is None:
                errors.append(error or f"backend_descriptors[{index}]_invalid")
                continue
            backend_kind = str(descriptor["backend_kind"])
            if production_mode and backend_kind in PROHIBITED_PRODUCTION_BACKEND_KINDS_V0:
                errors.append(f"production_placeholder_backend:{backend_kind}")
            if production_mode and backend_kind in REFERENCE_ONLY_PRODUCTION_BACKEND_KINDS_V0:
                errors.append(f"production_reference_backend:{backend_kind}")
            if production_mode and backend_kind == BACKEND_THRESHOLD_BLS_EXTERNAL_SERVICE:
                metadata = _require_mapping(descriptor.get("metadata", {}), name=f"backend_descriptors[{index}].metadata")
                provider_stack = metadata.get("provider_stack")
                if provider_stack not in APPROVED_EXTERNAL_THRESHOLD_BLS_PROVIDER_STACKS_V0:
                    errors.append("external_threshold_bls_provider_stack_not_approved")
                evidence_hash = metadata.get("external_threshold_bls_evidence_hash")
                try:
                    external_threshold_bls_evidence_hashes.add(
                        _require_root(evidence_hash, name="external_threshold_bls_evidence_hash")
                    )
                except (TypeError, ValueError) as exc:
                    errors.append(f"external_threshold_bls_evidence_hash_invalid:{_safe_governance_error(exc)}")
                if metadata.get("dealerless_dkg") is not True:
                    errors.append("external_threshold_bls_dealerless_dkg_required")
                if metadata.get("production_security_claim") is not True:
                    errors.append("external_threshold_bls_production_claim_required")
            if not descriptor["active"]:
                errors.append(f"backend_inactive:{descriptor['key_id']}")
            if not descriptor["no_raw_private_key_exposure"]:
                errors.append(f"backend_raw_private_key_exposure:{descriptor['key_id']}")
            backend_public.append(descriptor)
    backend_public.sort(key=lambda item: (str(item["key_id"]), str(item["backend_hash"])))

    required = frozenset(str(item).lower() for item in required_evidence_claims)
    normalized_claims, claim_errors = _normalize_evidence_claims(
        evidence_claims,
        required_claims=required,
        production_mode=production_mode,
    )
    errors.extend(claim_errors)
    if production_mode and external_threshold_bls_evidence_hashes:
        mpc_hashes = {
            str(item["evidence_hash"])
            for item in normalized_claims
            if item.get("claim_kind") == "mpc" and item.get("ok") is True and item.get("placeholder") is False
        }
        for evidence_hash in sorted(external_threshold_bls_evidence_hashes):
            if evidence_hash not in mpc_hashes:
                errors.append(f"external_threshold_bls_mpc_evidence_claim_missing:{evidence_hash}")

    body = {
        "schema": GOVERNANCE_AUTHORITY_RECEIPT_SCHEMA_V0,
        "action_id": normalized_action_id,
        "payload_kind": normalized_payload_kind,
        "payload_hash": normalized_payload_hash,
        "current_epoch": normalized_current_epoch,
        "proposal_epoch": normalized_proposal_epoch,
        "min_delay_epochs": normalized_min_delay,
        "production_mode": bool(production_mode),
        "quorum_report": quorum_report,
        "tau_policy_receipt_hash": tau_hash,
        "backend_hashes": [item["backend_hash"] for item in backend_public],
        "evidence_claims": normalized_claims,
        "ok": not errors,
        "errors": tuple(errors),
    }
    return {**body, "receipt_hash": hash_v0("zenodex_governance_authority_receipt_v0", body)}
