"""Structured readiness report for confidential cryptography surfaces.

The report is intentionally conservative. It records whether each confidential
surface has enough evidence for a production security claim; it does not treat a
configured external verifier or an alpha planner as a cryptographic proof.
"""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


CONFIDENTIAL_CRYPTO_READINESS_SCHEMA_V1 = "zenodex/confidential-crypto-readiness/v1"
_READINESS_HASH_DOMAIN_V1 = "zenodex.confidential_crypto_readiness/v1"


def build_confidential_crypto_readiness_v1(
    *,
    confidential_status: Mapping[str, Any] | None = None,
    attestation_status: Mapping[str, Any] | None = None,
    encrypted_sss_backup_status: Mapping[str, Any] | None = None,
    key_backend_descriptors: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build a fail-closed readiness report across TEE, SSS, MPC, and FHE."""

    conf = _mapping(confidential_status)
    attest = _mapping(attestation_status)
    sss = _mapping(encrypted_sss_backup_status)
    backends = tuple(_mapping(item) for item in (key_backend_descriptors or ()))
    surfaces = [
        _tee_surface(conf, attest),
        _sss_surface(sss),
        _mpc_surface(backends),
        _fhe_surface(conf),
    ]
    readiness_gaps = [
        f"{surface['id']}: {gap}"
        for surface in surfaces
        for gap in surface["readiness_gaps"]
    ]
    non_claims = sorted(
        {
            str(item)
            for surface in surfaces
            for item in surface["non_claims"]
        }
    )
    body: dict[str, Any] = {
        "schema": CONFIDENTIAL_CRYPTO_READINESS_SCHEMA_V1,
        "production_ready": all(bool(surface["production_ready"]) for surface in surfaces),
        "host_independent_ready": all(bool(surface["host_independent_ready"]) for surface in surfaces),
        "surfaces": surfaces,
        "readiness_gaps": readiness_gaps,
        "non_claims": non_claims,
    }
    body["readiness_hash"] = sha256_hex(
        domain_sep_bytes(_READINESS_HASH_DOMAIN_V1) + canonical_json_bytes(body)
    )
    return body


def _mapping(value: Mapping[str, Any] | None) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _bool(mapping: Mapping[str, Any], key: str) -> bool:
    return mapping.get(key) is True


def _int(mapping: Mapping[str, Any], key: str) -> int:
    value = mapping.get(key)
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else 0


def _root_hash(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    text = value.strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    return len(text) == 64 and all(ch in "0123456789abcdef" for ch in text)


def _surface(
    *,
    surface_id: str,
    state: str,
    implemented: bool,
    production_ready: bool,
    host_independent_ready: bool,
    evidence: Sequence[str],
    readiness_gaps: Sequence[str],
    non_claims: Sequence[str],
) -> dict[str, Any]:
    return {
        "id": surface_id,
        "state": state,
        "implemented": bool(implemented),
        "production_ready": bool(production_ready),
        "host_independent_ready": bool(host_independent_ready),
        "evidence": list(evidence),
        "readiness_gaps": list(readiness_gaps),
        "non_claims": list(non_claims),
    }


def _tee_surface(conf: Mapping[str, Any], attest: Mapping[str, Any]) -> dict[str, Any]:
    tee_enabled = _bool(conf, "tee_enabled")
    measurement_count = _int(conf, "approved_measurements_count")
    verifier_enabled = _bool(attest, "external_verifier_enabled")
    verifier_configured = _bool(attest, "external_verifier_configured")
    binding_hash_present = _root_hash(attest.get("external_verifier_binding_hash"))
    implemented = tee_enabled and measurement_count > 0
    operator_binding_ready = verifier_enabled and verifier_configured and binding_hash_present

    gaps: list[str] = []
    if not tee_enabled:
        gaps.append("TEE execution is disabled")
    if measurement_count <= 0:
        gaps.append("approved TEE measurement allowlist is empty")
    if not verifier_enabled:
        gaps.append("external TEE attestation verifier is disabled")
    if not verifier_configured:
        gaps.append("external TEE attestation verifier command is missing")
    if not binding_hash_present:
        gaps.append("external TEE verifier binding hash is missing")
    gaps.append("vendor attestation verifier semantics remain external to this repo")

    evidence = [
        f"approved_measurements_count={measurement_count}",
        f"external_verifier_enabled={verifier_enabled}",
        f"external_verifier_configured={verifier_configured}",
        f"external_verifier_binding_hash_present={binding_hash_present}",
    ]
    state = "external-verifier-bound" if operator_binding_ready else "external-verifier-missing"
    return _surface(
        surface_id="tee_attestation",
        state=state,
        implemented=implemented,
        production_ready=False,
        host_independent_ready=False,
        evidence=evidence,
        readiness_gaps=gaps,
        non_claims=(
            "does_not_prove_tee_hardware_confidentiality",
            "does_not_prove_vendor_attestation_soundness",
        ),
    )


def _sss_surface(sss: Mapping[str, Any]) -> dict[str, Any]:
    present = bool(sss)
    implemented = _bool(sss, "sss_implemented")
    ready = _bool(sss, "encrypted_sss_backup_ready")
    external_audit_ready = _bool(sss, "external_audit_ready")
    live_delivery_ready = _bool(sss, "live_provider_delivery_ready")
    replay_ready = _bool(sss, "replay_recovery_ready")
    hostile_replay_ready = _bool(sss, "replay_hostile_tests_ready")
    raw_material_absent = _bool(sss, "raw_material_absent")
    no_server_reconstitution = sss.get("server_side_reconstitution") is False

    gaps: list[str] = []
    if not present:
        gaps.append("encrypted SSS backup status is missing")
    if present and not implemented:
        gaps.append("SSS algorithm is not reported as implemented")
    if present and not ready:
        gaps.append("encrypted SSS backup evaluator is blocked")
    if present and not external_audit_ready:
        gaps.append("external SSS audit evidence is not ready")
    if present and not live_delivery_ready:
        gaps.append("live SSS provider delivery evidence is not ready")
    if present and not replay_ready:
        gaps.append("SSS recovery drill was not replay-verified")
    if present and not hostile_replay_ready:
        gaps.append("hostile SSS replay tests are not ready")
    if present and not raw_material_absent:
        gaps.append("SSS status does not prove raw material absence")
    if present and not no_server_reconstitution:
        gaps.append("SSS status does not rule out server-side reconstitution")

    production_ready = (
        ready
        and implemented
        and external_audit_ready
        and live_delivery_ready
        and replay_ready
        and hostile_replay_ready
        and raw_material_absent
        and no_server_reconstitution
    )
    state = "audit-bound-production-candidate" if production_ready else ("fixture-or-beta-only" if present else "missing")
    return _surface(
        surface_id="sss_backup",
        state=state,
        implemented=implemented,
        production_ready=production_ready,
        host_independent_ready=production_ready,
        evidence=(
            f"encrypted_sss_status_present={present}",
            f"encrypted_sss_backup_ready={ready}",
            f"external_audit_ready={external_audit_ready}",
            f"live_provider_delivery_ready={live_delivery_ready}",
            f"replay_recovery_ready={replay_ready}",
            f"replay_hostile_tests_ready={hostile_replay_ready}",
        ),
        readiness_gaps=gaps,
        non_claims=(
            "does_not_claim_audited_production_sss_custody",
            "does_not_claim_encrypted_sss_runtime_present_without_status",
        ),
    )


def _mpc_surface(backends: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    mpc_backends = [
        backend
        for backend in backends
        if "mpc" in str(backend.get("backend_kind") or "").lower()
    ]
    placeholder_count = sum(
        1
        for backend in mpc_backends
        if str(backend.get("backend_kind") or "") == "mpc-placeholder"
    )
    real_backend_count = len(mpc_backends) - placeholder_count
    gaps: list[str] = []
    if not mpc_backends:
        gaps.append("MPC backend is not wired")
    if placeholder_count:
        gaps.append("MPC backend is still a placeholder")
    if real_backend_count:
        gaps.append("MPC protocol security evidence is not represented in this repo")
    state = "placeholder-only" if placeholder_count else "missing"
    if real_backend_count:
        state = "external-backend-unclassified"
    return _surface(
        surface_id="mpc",
        state=state,
        implemented=real_backend_count > 0,
        production_ready=False,
        host_independent_ready=False,
        evidence=(
            f"mpc_backend_count={len(mpc_backends)}",
            f"mpc_placeholder_count={placeholder_count}",
            f"mpc_real_backend_count={real_backend_count}",
        ),
        readiness_gaps=gaps,
        non_claims=("does_not_claim_secure_multiparty_computation",),
    )


def _fhe_surface(conf: Mapping[str, Any]) -> dict[str, Any]:
    alpha_enabled = _bool(conf, "fhe_alpha_enabled")
    gaps = [
        "FHE surface is an alpha planner, not production FHE cryptography",
        "production FHE backend, key management, and decryption policy are not wired",
    ]
    if alpha_enabled:
        gaps.append("FHE alpha is enabled and must stay disabled for beta posture")
    return _surface(
        surface_id="fhe",
        state="alpha-enabled" if alpha_enabled else "alpha-disabled",
        implemented=False,
        production_ready=False,
        host_independent_ready=False,
        evidence=(f"fhe_alpha_enabled={alpha_enabled}",),
        readiness_gaps=gaps,
        non_claims=("does_not_claim_production_fhe_confidentiality",),
    )
