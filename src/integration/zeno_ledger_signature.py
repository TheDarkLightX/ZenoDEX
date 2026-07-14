"""Signed envelopes for ZenoLedger artifacts."""

from __future__ import annotations

import hashlib
import hmac
from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x, hex_to_bytes_fixed

try:
    from py_ecc.bls import G2Basic
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency guard
    G2Basic = None
    _BLS12_381_CURVE_ORDER = None
    _BLS_AVAILABLE = False


SIGNED_ARTIFACT_ENVELOPE_SCHEMA_V0 = "zenodex/zeno_ledger/signed_artifact_envelope/v0"
SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0 = "hmac-sha256-testnet-v0"
SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0 = "bls12-381-g2-basic-release-v0"

SUPPORTED_SIGNATURE_ALGORITHMS_V0 = frozenset(
    {
        SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
        SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
    }
)

SUPPORTED_PAYLOAD_KINDS_V0 = frozenset(
    {
        "watcher_attestation",
        "mirror_index",
        "tau_export_packet",
        "checkpoint",
        "public_network_config",
        "oracle_authority_profile",
        "perps_wallet_authority_profile",
        "perps_wallet_recovery_exercise",
        "perps_wallet_rotation_exercise",
        "governance_action",
        "zrpf_spot_v7_operational_policy",
        "zrpf_sampled_retrievability_response",
        "perps_wallet_encrypted_sss_audit_evidence",
        "perps_wallet_sss_production_ceremony",
        "perps_wallet_sss_custodian_registry",
        "perps_wallet_sss_key_rotation_ceremony",
    }
)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_secret(secret_hex: str) -> bytes:
    canonical = canonical_hex_fixed_allow_0x(secret_hex, nbytes=32, name="secret_hex")
    if secret_hex != canonical:
        raise ValueError("secret_hex must be canonical lowercase 0x-prefixed hex")
    return hex_to_bytes_fixed(canonical, nbytes=32, name="secret_hex")


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise RuntimeError("py_ecc.bls is required for BLS release signatures")


def _require_bls_basic() -> Any:
    _require_bls()
    if G2Basic is None:
        raise RuntimeError("py_ecc.bls is required for BLS release signatures")
    return G2Basic


def _require_bls_private_key(private_key_hex: str) -> int:
    canonical = canonical_hex_fixed_allow_0x(private_key_hex, nbytes=32, name="bls_private_key_hex")
    if private_key_hex != canonical:
        raise ValueError("bls_private_key_hex must be canonical lowercase 0x-prefixed hex")
    raw = hex_to_bytes_fixed(canonical, nbytes=32, name="bls_private_key_hex")
    sk = int.from_bytes(raw, byteorder="big", signed=False)
    if sk <= 0:
        raise ValueError("bls_private_key_hex must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("bls_private_key_hex out of range")
    return sk


def _require_bls_public_key(public_key_hex: str, *, name: str = "public_key") -> str:
    canonical = canonical_hex_fixed_allow_0x(public_key_hex, nbytes=48, name=name)
    if public_key_hex != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_bls_signature(signature_hex: str) -> str:
    canonical = canonical_hex_fixed_allow_0x(signature_hex, nbytes=96, name="signature")
    if signature_hex != canonical:
        raise ValueError("signature must be canonical lowercase 0x-prefixed hex")
    return canonical


def _signature_body(
    *,
    payload_kind: str,
    payload_hash: str,
    signer_id: str,
    key_id: str,
    algorithm: str,
    public_key: str | None = None,
) -> dict[str, Any]:
    kind = _require_str(payload_kind, name="payload_kind")
    if kind not in SUPPORTED_PAYLOAD_KINDS_V0:
        raise ValueError("payload_kind is not supported")
    if algorithm not in SUPPORTED_SIGNATURE_ALGORITHMS_V0:
        raise ValueError("algorithm is not supported")
    body = {
        "schema": SIGNED_ARTIFACT_ENVELOPE_SCHEMA_V0,
        "algorithm": algorithm,
        "payload_kind": kind,
        "payload_hash": _require_root(payload_hash, name="payload_hash"),
        "signer_id": _require_str(signer_id, name="signer_id"),
        "key_id": _require_str(key_id, name="key_id"),
    }
    if algorithm == SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0:
        if public_key is None:
            raise ValueError("public_key is required for BLS release signatures")
        body["public_key"] = _require_bls_public_key(public_key)
    elif public_key is not None:
        raise ValueError("public_key is only supported for BLS release signatures")
    return body


def _signature_message_digest(body: Mapping[str, Any]) -> bytes:
    return hashlib.sha256(
        canonical_json_bytes_v0(
            {
                "domain": "zenodex.zeno_ledger.signed_artifact.v0",
                "body": dict(body),
            }
        )
    ).digest()


def _compute_signature(*, body: Mapping[str, Any], secret_hex: str) -> str:
    secret = _require_secret(secret_hex)
    mac = hmac.new(
        secret,
        canonical_json_bytes_v0(
            {
                "domain": "zenodex.zeno_ledger.signed_artifact.v0",
                "body": dict(body),
            }
        ),
        hashlib.sha256,
    ).hexdigest()
    return "0x" + mac


def _compute_bls_signature(*, body: Mapping[str, Any], private_key_hex: str) -> str:
    bls = _require_bls_basic()
    sk = _require_bls_private_key(private_key_hex)
    signature = bls.Sign(sk, _signature_message_digest(body))
    return "0x" + signature.hex()


def bls_public_key_hex_from_private_key_v0(private_key_hex: str) -> str:
    bls = _require_bls_basic()
    sk = _require_bls_private_key(private_key_hex)
    return "0x" + bls.SkToPk(sk).hex()


def build_signed_artifact_envelope_v0(
    *,
    payload_kind: str,
    payload_hash: str,
    signer_id: str,
    key_id: str,
    secret_hex: str,
) -> dict[str, Any]:
    """Build a deterministic HMAC-signed envelope over an artifact hash."""

    body = _signature_body(
        payload_kind=payload_kind,
        payload_hash=payload_hash,
        signer_id=signer_id,
        key_id=key_id,
        algorithm=SIGNED_ARTIFACT_ALGORITHM_HMAC_SHA256_V0,
    )
    signature = _compute_signature(body=body, secret_hex=secret_hex)
    envelope = {**body, "signature": signature}
    return {**envelope, "envelope_hash": hash_v0("signed_artifact_envelope_v0", envelope)}


def build_bls_signed_artifact_envelope_v0(
    *,
    payload_kind: str,
    payload_hash: str,
    signer_id: str,
    key_id: str,
    private_key_hex: str,
) -> dict[str, Any]:
    """Build a BLS12-381 public-key signed envelope over an artifact hash."""

    public_key = bls_public_key_hex_from_private_key_v0(private_key_hex)
    body = _signature_body(
        payload_kind=payload_kind,
        payload_hash=payload_hash,
        signer_id=signer_id,
        key_id=key_id,
        algorithm=SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        public_key=public_key,
    )
    signature = _compute_bls_signature(body=body, private_key_hex=private_key_hex)
    envelope = {**body, "signature": signature}
    return {**envelope, "envelope_hash": hash_v0("signed_artifact_envelope_v0", envelope)}


def validate_signed_artifact_envelope_v0(
    *,
    envelope: Mapping[str, Any],
    expected_payload_kind: str,
    expected_payload_hash: str,
    secret_hex: str,
) -> None:
    obj = _require_mapping(envelope, name="envelope")
    expected = build_signed_artifact_envelope_v0(
        payload_kind=expected_payload_kind,
        payload_hash=expected_payload_hash,
        signer_id=_require_str(obj.get("signer_id"), name="envelope.signer_id"),
        key_id=_require_str(obj.get("key_id"), name="envelope.key_id"),
        secret_hex=secret_hex,
    )
    if dict(obj) != expected:
        raise ValueError("signed artifact envelope binding mismatch")


def validate_bls_signed_artifact_envelope_v0(
    *,
    envelope: Mapping[str, Any],
    expected_payload_kind: str,
    expected_payload_hash: str,
    expected_public_key: str,
) -> None:
    obj = _require_mapping(envelope, name="envelope")
    public_key = _require_bls_public_key(expected_public_key, name="expected_public_key")
    body = _signature_body(
        payload_kind=expected_payload_kind,
        payload_hash=expected_payload_hash,
        signer_id=_require_str(obj.get("signer_id"), name="envelope.signer_id"),
        key_id=_require_str(obj.get("key_id"), name="envelope.key_id"),
        algorithm=SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0,
        public_key=public_key,
    )
    expected_keys = set(body.keys()) | {"signature", "envelope_hash"}
    if set(obj.keys()) != expected_keys:
        raise ValueError("signed artifact envelope keys mismatch")
    if str(obj.get("public_key")) != public_key:
        raise ValueError("signed artifact envelope public_key mismatch")
    signature = _require_bls_signature(_require_str(obj.get("signature"), name="envelope.signature"))
    bls = _require_bls_basic()
    ok = bool(
        bls.Verify(
            hex_to_bytes_fixed(public_key, nbytes=48, name="public_key"),
            _signature_message_digest(body),
            hex_to_bytes_fixed(signature, nbytes=96, name="signature"),
        )
    )
    if not ok:
        raise ValueError("signed artifact envelope BLS signature invalid")
    envelope = {**body, "signature": signature}
    expected = {**envelope, "envelope_hash": hash_v0("signed_artifact_envelope_v0", envelope)}
    if dict(obj) != expected:
        raise ValueError("signed artifact envelope binding mismatch")


def infer_artifact_hash_v0(*, artifact: Mapping[str, Any], payload_kind: str) -> str:
    obj = _require_mapping(artifact, name="artifact")
    kind = _require_str(payload_kind, name="payload_kind")
    if kind == "watcher_attestation":
        return _require_root(obj.get("attestation_hash"), name="artifact.attestation_hash")
    if kind == "mirror_index":
        return _require_root(obj.get("mirror_index_hash"), name="artifact.mirror_index_hash")
    if kind == "tau_export_packet":
        return _require_root(obj.get("packet_hash"), name="artifact.packet_hash")
    if kind == "checkpoint":
        return _require_root(obj.get("checkpoint_hash"), name="artifact.checkpoint_hash")
    if kind == "oracle_authority_profile":
        return _require_root(obj.get("authority_hash"), name="artifact.authority_hash")
    if kind == "perps_wallet_authority_profile":
        return _require_root(obj.get("wallet_authority_hash"), name="artifact.wallet_authority_hash")
    if kind == "perps_wallet_recovery_exercise":
        return _require_root(obj.get("exercise_hash"), name="artifact.exercise_hash")
    if kind == "perps_wallet_rotation_exercise":
        return _require_root(obj.get("exercise_hash"), name="artifact.exercise_hash")
    raise ValueError("payload_kind is not supported")
